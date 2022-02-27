package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.autoSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import java.util.UUID

interface MutableBackstackNavigationController<T> : BackstackState<T> {
    override val entryMap: MutableBackstackMap<T>

    override var currentEntryId: UUID
}

val <T> MutableBackstackNavigationController<T>.canNavigateBack
    get() = currentEntry.previous != null

@Composable
fun <T> rememberMutableBackstackNavigationController(
    initialBackstackEntries: List<BackstackEntry<T>>,
    saver: Saver<T, Any> = autoSaver(),
): MutableBackstackNavigationController<T> =
    rememberMutableBackstackNavigationController(
        initialBackstackEntries = initialBackstackEntries,
        backstackValueSaverFactory = { saver }
    )

@Composable
fun <T> rememberMutableBackstackNavigationController(
    initialBackstackEntries: List<BackstackEntry<T>>,
    backstackValueSaverFactory: BackstackValueSaverFactory<T>,
): MutableBackstackNavigationController<T> {
    require(initialBackstackEntries.isNotEmpty())

    val backstackMap = rememberBackstackMap(
        initialBackstackEntries = initialBackstackEntries,
        backstackValueSaverFactory = backstackValueSaverFactory
    )

    var currentBackstackEntryId by rememberSaveable(
        saver = Saver(
            save = { it.value.toString() },
            restore = { mutableStateOf(UUID.fromString(it)) }
        )
    ) {
        mutableStateOf(initialBackstackEntries.last().id)
    }

    return remember {
        object : MutableBackstackNavigationController<T> {
            override val entryMap: MutableBackstackMap<T> get() = backstackMap
            override var currentEntryId: UUID
                get() = currentBackstackEntryId
                set(value) {
                    currentBackstackEntryId = value
                }
        }
    }
}

/**
 * Guards running the block against whether the actor (that is, the one running this function) is expected.
 *
 * If [actorEntryId] is not `null,` then [block] will only be run if the
 * [MutableBackstackNavigationController.currentEntryId] at the time of invocation matches the
 * [actorEntryId].
 * If [actorEntryId] is `null`, then [block] will always be run.
 *
 * This function returns `true` if and only if the [block] was run.
 */
fun <T> MutableBackstackNavigationController<T>.withExpectedActor(
    actorEntryId: UUID?,
    block: MutableBackstackNavigationController<T>.(currentEntry: BackstackEntry<T>) -> Unit
): Boolean =
    if (actorEntryId == null || actorEntryId == currentEntry.id) {
        block(currentEntry)
        true
    } else {
        false
    }

fun <T> MutableBackstackNavigationController<T>.popUpTo(
    entryPredicate: (BackstackEntry<T>) -> Boolean,
    inclusive: Boolean = false,
) {
    currentEntryId = entryMap.popUpTo(
        topOfBackstackId = currentEntryId,
        entryPredicate = entryPredicate,
        inclusive = inclusive
    )
}

fun <T> MutableBackstackNavigationController<T>.popUpTo(
    id: UUID,
    inclusive: Boolean = false,
) {
    val predicate: (BackstackEntry<T>) -> Boolean = { it.id == id }
    popUpTo(
        entryPredicate = predicate,
        inclusive = inclusive,
    )
}

@JvmName("popUpToValue")
fun <T> MutableBackstackNavigationController<T>.popUpTo(
    predicate: (T) -> Boolean,
    inclusive: Boolean = false,
) {
    val entryPredicate: (BackstackEntry<T>) -> Boolean = { predicate(it.value) }
    popUpTo(
        entryPredicate = entryPredicate,
        inclusive = inclusive,
    )
}

fun <T> MutableBackstackNavigationController<T>.navigate(
    valueFactory: (previous: BackstackEntry<T>) -> T,
    id: UUID = UUID.randomUUID(),
) {
    currentEntryId = entryMap.navigate(
        topOfBackstackId = currentEntryId,
        valueFactory = valueFactory,
        id = id
    )
}

fun <T> MutableBackstackNavigationController<T>.navigate(
    value: T,
    id: UUID = UUID.randomUUID(),
) = navigate(
    valueFactory = { value },
    id = id,
)

fun <T> MutableBackstackNavigationController<T>.popBackstack() {
    currentEntryId = entryMap.popBackstack(
        topOfBackstackId = currentEntryId,
    )
}
