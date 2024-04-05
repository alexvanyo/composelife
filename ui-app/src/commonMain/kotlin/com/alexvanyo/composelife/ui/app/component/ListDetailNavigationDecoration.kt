package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Composable
import androidx.compose.runtime.State
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackMap
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationDecoration
import java.util.UUID

fun <T> listDetailNavigationDecoration(
    navigationDecoration: NavigationDecoration<BackstackEntry<T>, BackstackState<T>>,
    onBackButtonPressed: () -> Unit,
): NavigationDecoration<BackstackEntry<T>, BackstackState<T>> = { pane ->
    val currentPane by rememberUpdatedState(pane)

    val idsTransform = entryMap
        .filterValues { it.value !is ListMarker }
        .mapValues { (_, entry) ->
            when (entry.value) {
                is DetailMarker -> entry.previous!!.id
                else -> entry.id
            }
        }

    val transformedPaneMap: Map<UUID, State<@Composable (BackstackEntry<T>) -> Unit>> = entryMap
        .filterValues { it.value !is ListMarker }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailMarker) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (id, entry) ->
            key(id) {
                rememberUpdatedState(
                    when (entry.value) {
                        is DetailMarker -> {
                            {
                                val previous = entry.previous
                                requireNotNull(previous)
                                val listMarker = previous.value as ListMarker
                                val detailMarker = entry.value as DetailMarker

                                ListDetailPaneScaffold(
                                    showList = listMarker.isListVisible,
                                    showDetail = detailMarker.isDetailVisible,
                                    listContent = {
                                        currentPane(previous)
                                    },
                                    detailContent = {
                                        currentPane(entry)
                                    },
                                    onBackButtonPressed = onBackButtonPressed,
                                )
                            }
                        }

                        else -> {
                            {
                                currentPane(entry)
                            }
                        }
                    }
                )
            }
        }

    val transformedPane: @Composable (BackstackEntry<T>) -> Unit = { entry ->
        key(entry.id) {
            val transformedPane by remember { transformedPaneMap.getValue(entry.id) }
            transformedPane.invoke(entry)
        }
    }

    val transformedEntryMap = entryMap
        .filterValues { it.value !is ListMarker }
        .mapKeys { (_, entry) ->
            if (entry.value is DetailMarker) {
                entry.previous!!.id
            } else {
                entry.id
            }
        }
        .mapValues { (_, entry) ->
            if (entry.value is DetailMarker) {
                BackstackEntry(
                    entry.value,
                    previous = entry.previous!!.previous,
                    id = entry.previous!!.id
                )
            } else {
                entry
            }
        }
    val transformedCurrentEntryId = idsTransform.getValue(currentEntryId)

    val transformedBackstackState: BackstackState<T> =
        object : BackstackState<T> {
            override val entryMap: BackstackMap<T>
                get() = transformedEntryMap
            override val currentEntryId: UUID
                get() = transformedCurrentEntryId

        }

    navigationDecoration.invoke(transformedBackstackState, transformedPane)
}

interface ListMarker : ListDetailInfo

interface DetailMarker : ListDetailInfo

interface ListDetailInfo {
    val isListVisible: Boolean
    val isDetailVisible: Boolean
}
