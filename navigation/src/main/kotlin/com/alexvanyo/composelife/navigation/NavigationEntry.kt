package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Stable
import java.util.UUID

/**
 * An entry in navigation. An entry just needs to have an identifying [id], which is unique among all entries.
 */
@Stable
interface NavigationEntry {
    val id: UUID
}
