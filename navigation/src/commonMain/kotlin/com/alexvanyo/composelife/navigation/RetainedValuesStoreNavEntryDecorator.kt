package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.retain.RetainedValuesStoreRegistry
import androidx.compose.runtime.retain.retainRetainedValuesStoreRegistry
import androidx.navigation3.runtime.NavEntryDecorator

@Composable
public fun <T : Any> rememberRetainedValuesStoreNavEntryDecorator(
    retainedValuesStoreRegistry: RetainedValuesStoreRegistry = retainRetainedValuesStoreRegistry()
): RetainedValuesStoreNavEntryDecorator<T> =
    remember(retainedValuesStoreRegistry) { RetainedValuesStoreNavEntryDecorator(retainedValuesStoreRegistry) }

public class RetainedValuesStoreNavEntryDecorator<T : Any>(
    retainedValuesStoreRegistry: RetainedValuesStoreRegistry
) :
    NavEntryDecorator<T>(
        onPop = { contentKey -> retainedValuesStoreRegistry.clearChild(contentKey) },
        decorate = { entry ->
            retainedValuesStoreRegistry.LocalRetainedValuesStoreProvider(entry.contentKey) { entry.Content() }
        },
    )
