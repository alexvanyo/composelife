/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife

import com.alexvanyo.composelife.algorithm.di.AlgorithmModule
import com.alexvanyo.composelife.clock.di.ClockModule
import com.alexvanyo.composelife.data.di.RepositoryModule
import com.alexvanyo.composelife.dispatchers.di.DispatchersModule
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.random.di.RandomModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.ui.app.ComposeLifeAppInjectEntryPoint
import com.alexvanyo.composelife.updatable.di.UpdatableModule

class MainActivityInjectEntryPoint<T>(
    applicationComponent: T,
) : RandomModule by applicationComponent,
    ClockModule by applicationComponent,
    RepositoryModule by applicationComponent,
    AlgorithmModule by applicationComponent,
    DispatchersModule by applicationComponent,
    PreferencesModule by applicationComponent,
    UpdatableModule by applicationComponent,
    ComposeLifePreferencesProvider,
    ComposeLifeAppInjectEntryPoint
    where T : ApplicationComponent,
          T : ClockModule,
          T : RandomModule,
          T : RepositoryModule,
          T : AlgorithmModule,
          T : DispatchersModule,
          T : PreferencesModule,
          T : UpdatableModule
