package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Stable
import java.util.UUID

@Stable
interface NavigationEntry {
    val id: UUID
}
