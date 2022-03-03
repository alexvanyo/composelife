package com.alexvanyo.composelife.ui.entrypoints

import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject

@HiltViewModel
class ComposeLifeDispatchersEntryPoint @Inject constructor(
    val dispatchers: ComposeLifeDispatchers
) : ViewModel()
