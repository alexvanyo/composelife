package com.alexvanyo.composelife.ui.entrypoints

import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject

@HiltViewModel
class ComposeLifePreferencesEntryPoint @Inject constructor(
    val composeLifePreferences: ComposeLifePreferences
) : ViewModel()
