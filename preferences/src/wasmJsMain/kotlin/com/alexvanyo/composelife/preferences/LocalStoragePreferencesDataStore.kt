/*
 * Copyright 2025 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.preferences

import androidx.datastore.core.DataStore
import androidx.datastore.core.DataStoreFactory
import androidx.datastore.core.InterProcessCoordinator
import androidx.datastore.core.ReadScope
import androidx.datastore.core.Storage
import androidx.datastore.core.StorageConnection
import androidx.datastore.core.WriteScope
import androidx.datastore.core.okio.OkioSerializer
import androidx.datastore.core.use
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import com.alexvanyo.composelife.scopes.LocalStorage
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.Binds
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.ForScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoSet
import dev.zacsweers.metro.Qualifier
import dev.zacsweers.metro.SingleIn
import kotlinx.browser.window
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.asPromise
import kotlinx.coroutines.async
import kotlinx.coroutines.await
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.channels.BufferOverflow
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.MutableSharedFlow
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext
import okio.Buffer
import okio.ByteString.Companion.decodeBase64
import org.w3c.dom.events.Event
import kotlin.js.Promise

@Qualifier
annotation class PreferencesProtoItemKey

@ContributesTo(AppScope::class)
@BindingContainer
interface LocalStoragePreferencesDataStoreBindings {
    @Binds
    val LocalStoragePreferencesDataStore.bind: PreferencesDataStore

    @Binds
    @IntoSet
    @ForScope(AppScope::class)
    val LocalStoragePreferencesDataStore.bindIntoUpdatable: Updatable
}

@SingleIn(AppScope::class)
@Inject
class LocalStoragePreferencesDataStore(
    @param:LocalStorage private val storage: org.w3c.dom.Storage,
    private val navigator: org.w3c.dom.Navigator,
    @param:PreferencesProtoItemKey private val itemKey: String,
    private val dispatchers: ComposeLifeDispatchers,
) : PreferencesDataStore, Updatable {
    private val mutex = Mutex()

    private val dataStoreCompletable = CompletableDeferred<DataStore<PreferencesProto>>()

    override suspend fun getDataStore(): DataStore<PreferencesProto> = dataStoreCompletable.await()

    private val localStorageUpdates = MutableSharedFlow<Unit>(
        replay = 1,
        onBufferOverflow = BufferOverflow.DROP_OLDEST,
    )

    override suspend fun update(): Nothing = mutex.withLock {
        withContext(dispatchers.IO) {
            coroutineScope {
                dataStoreCompletable.complete(
                    createDataStore(this),
                )
                window.observeEvents("storage") {
                    localStorageUpdates.tryEmit(Unit)
                }
            }
        }
    }

    private fun createDataStore(
        scope: CoroutineScope,
    ): DataStore<PreferencesProto> =
        DataStoreFactory.create(
            storage = WebStorage(
                storage = storage,
                navigator = navigator,
                updateNotifications = localStorageUpdates,
                itemKey = itemKey,
                serializer = serializer,
            ),
            corruptionHandler = corruptionHandler,
            migrations = migrations,
            scope = scope,
        )
}

private class WebProcessCoordinator(
    private val storage: org.w3c.dom.Storage,
    navigator: org.w3c.dom.Navigator,
    override val updateNotifications: Flow<Unit>,
) : InterProcessCoordinator {
    private val locks = getLocks(navigator)

    @OptIn(ExperimentalWasmJsInterop::class)
    override suspend fun <T> lock(block: suspend () -> T): T =
        locks.withLock(preferencesLockName) {
            block()
        }

    @OptIn(ExperimentalWasmJsInterop::class)
    override suspend fun <T> tryLock(block: suspend (Boolean) -> T): T =
        locks.withLock(preferencesLockName, ifAvailable = true) { lock ->
            block(lock != null)
        }

    @OptIn(ExperimentalWasmJsInterop::class)
    override suspend fun getVersion(): Int =
        locks.withLock(versionLockName) {
            storage.getItem(preferencesVersionItemKey)?.toIntOrNull() ?: 0
        }

    @OptIn(ExperimentalWasmJsInterop::class)
    override suspend fun incrementAndGetVersion(): Int =
        locks.withLock(versionLockName) {
            val oldValue = storage.getItem(preferencesVersionItemKey)?.toIntOrNull() ?: 0
            val newValue = oldValue + 1
            storage.setItem(preferencesVersionItemKey, newValue.toString())
            newValue
        }

    companion object {
        private const val preferencesLockName = "preferencesLock"
        private const val versionLockName = "versionLock"
        private const val preferencesVersionItemKey = "preferencesVersion"
    }
}

private class WebStorage<T>(
    val storage: org.w3c.dom.Storage,
    val navigator: org.w3c.dom.Navigator,
    val updateNotifications: Flow<Unit>,
    val itemKey: String,
    val serializer: OkioSerializer<T>,
) : Storage<T> {
    override fun createConnection(): StorageConnection<T> =
        WebStorageConnection(storage, navigator, updateNotifications, itemKey, serializer)
}

private class WebStorageConnection<T>(
    val storage: org.w3c.dom.Storage,
    val navigator: org.w3c.dom.Navigator,
    val updateNotifications: Flow<Unit>,
    val itemKey: String,
    val serializer: OkioSerializer<T>,
) : StorageConnection<T> {
    override val coordinator: InterProcessCoordinator = WebProcessCoordinator(
        storage = storage,
        navigator = navigator,
        updateNotifications = updateNotifications,
    )

    private val transactionMutex = Mutex()

    override suspend fun <R> readScope(block: suspend ReadScope<T>.(locked: Boolean) -> R): R {
        val lock = transactionMutex.tryLock()
        return try {
            WebStorageReadScope(storage, itemKey, serializer).use { readScope ->
                block(readScope, lock)
            }
        } finally {
            if (lock) {
                transactionMutex.unlock()
            }
        }
    }

    override suspend fun writeScope(block: suspend WriteScope<T>.() -> Unit) {
        transactionMutex.withLock {
            WebStorageWriteScope(storage, itemKey, serializer).use { writeScope ->
                block(writeScope)
            }
        }
    }

    override fun close() = Unit
}

private open class WebStorageReadScope<T>(
    val storage: org.w3c.dom.Storage,
    val itemKey: String,
    val serializer: OkioSerializer<T>,
) : ReadScope<T> {
    override suspend fun readData(): T {
        val item = storage.getItem(itemKey)
        return if (item == null || item.isEmpty()) {
            serializer.defaultValue
        } else {
            val source = Buffer().write(
                checkNotNull(item.decodeBase64()) {
                    "Written value wasn't able to be decoded properly"
                },
            )
            try {
                serializer.readFrom(source)
            } finally {
                source.close()
            }
        }
    }

    override fun close() = Unit
}

private class WebStorageWriteScope<T>(
    storage: org.w3c.dom.Storage,
    itemKey: String,
    serializer: OkioSerializer<T>,
) : WebStorageReadScope<T>(
    storage,
    itemKey,
    serializer,
), WriteScope<T> {
    override suspend fun writeData(value: T) {
        val sink = Buffer()
        try {
            serializer.writeTo(value, sink)
            storage.setItem(itemKey, sink.readByteString().base64())
        } finally {
            sink.close()
        }
    }
}

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
internal fun getLocks(navigator: org.w3c.dom.Navigator): LockManager =
    js("navigator.locks")

internal external class Lock

internal external class LockManager

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun <T : JsAny?> requestLockWithPromise(
    lockManager: LockManager,
    name: String,
    ifAvailable: Boolean,
    block: (Lock?) -> Promise<T>,
): Promise<T> =
    js("lockManager.request(name, { ifAvailable: ifAvailable }, block)")

@OptIn(ExperimentalWasmJsInterop::class)
private suspend fun <T : JsAny?> LockManager.withLockJs(
    name: String,
    ifAvailable: Boolean = false,
    block: suspend (Lock?) -> T,
): T =
    coroutineScope {
        requestLockWithPromise(
            this@withLockJs,
            name = name,
            ifAvailable = ifAvailable,
        ) { lock ->
            async {
                block(lock)
            }.asPromise()
        }.await()
    }

@OptIn(ExperimentalWasmJsInterop::class)
private suspend fun <T> LockManager.withLock(
    name: String,
    ifAvailable: Boolean = false,
    block: suspend (Lock?) -> T,
): T = withLockJs(name, ifAvailable) { lock ->
    Result.success(block(lock)).toJsReference()
}.get().getOrThrow()

private suspend fun org.w3c.dom.Window.observeEvents(
    type: String,
    callback: (event: Event) -> Unit,
): Nothing {
    addEventListener(type, callback)
    try {
        awaitCancellation()
    } finally {
        removeEventListener(type, callback)
    }
}
