package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Stable
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.autoSaver
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import java.util.UUID

/**
 * An entry in the backstack.
 *
 * This is a stable pair between an unique [id], and an arbitrary [value] of type [T].
 *
 * [BackstackEntry] is [Stable], meaning that [value] must also be [Stable] as anything observing backstack entries
 * will want to observe if any relevant state changes.
 */
@Stable
class BackstackEntry<T>(
    val value: T,
    val id: UUID = UUID.randomUUID(),
) {

    /**
     * The [Saver] for a [BackstackEntry], which delegates saving the [value] to the provided [valueSaver].
     */
    class Saver<T>(
        private val valueSaver: androidx.compose.runtime.saveable.Saver<T, Any>,
    ) : androidx.compose.runtime.saveable.Saver<BackstackEntry<T>, Any> by listSaver(
        save = { entry ->
            listOf(
                with(valueSaver) { save(entry.value) },
                entry.id.toString(),
            )
        },
        restore = { list ->
            @Suppress("UNCHECKED_CAST")
            BackstackEntry(
                value = valueSaver.restore(list[0] as Any) as T,
                id = UUID.fromString(list[1] as String)
            )
        }
    )
}

/**
 * A mutable backstack is simply a [MutableList] of [BackstackEntry]s.
 */
typealias MutableBackstack<T> = MutableList<BackstackEntry<T>>

/**
 * A backstack is simply a [List] of [BackstackEntry]s.
 */
typealias Backstack<T> = List<BackstackEntry<T>>

/**
 * Remembers a [MutableBackstack] of type [T], with the given [initialBackstack], and saving for each entry value done
 * by [saver].
 */
@Composable
fun <T> rememberBackstack(
    initialBackstack: Backstack<T>,
    saver: Saver<T, Any> = autoSaver(),
) = rememberBackstack(
    initialBackstack = initialBackstack,
    partialBackstackSaverFactory = saver.asPartialBackstackSaverFactory()
)

/**
 * A more advanced version of [rememberBackstack] that allows saving and restoring state with knowledge of the partial
 * backstack (that is, all previous destinations in the stack).
 */
@Composable
fun <T> rememberBackstack(
    initialBackstack: Backstack<T>,
    partialBackstackSaverFactory: PartialBackstackSaverFactory<T>,
): MutableBackstack<T> =
    rememberSaveable(
        saver = listSaver(
            save = { backstack ->
                backstack.mapIndexed { index, entry ->
                    with(BackstackEntry.Saver(partialBackstackSaverFactory.create(backstack.subList(0, index)))) {
                        save(entry)
                    }
                }
            },
            restore = { list ->
                mutableStateListOf<BackstackEntry<T>>().apply {
                    val partialBackstack = mutableListOf<BackstackEntry<T>>()
                    list.forEach {
                        partialBackstack.add(
                            BackstackEntry.Saver(
                                partialBackstackSaverFactory.create(partialBackstack)
                            ).restore(it!!)!!
                        )
                    }
                    addAll(partialBackstack)
                }
            }
        )
    ) {
        mutableStateListOf<BackstackEntry<T>>().apply {
            addAll(initialBackstack)
        }
    }

/**
 * A factory for creating a [Saver] that has knowledge of the partial backstack, which is the backstack above the
 * entry being restored or saved.
 *
 * Note that partial backstack can be empty, if saving or restoring the first entry.
 */
fun interface PartialBackstackSaverFactory<T> {
    fun create(partialBackstack: Backstack<T>): Saver<T, Any>
}

/**
 * Creates a trivial [PartialBackstackSaverFactory] for a [Saver] that doesn't care about the partial backstack.
 */
fun <T> Saver<T, Any>.asPartialBackstackSaverFactory(): PartialBackstackSaverFactory<T> =
    PartialBackstackSaverFactory { this }
