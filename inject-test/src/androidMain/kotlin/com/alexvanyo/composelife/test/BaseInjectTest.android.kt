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

package com.alexvanyo.composelife.test

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.ApplicationComponentArguments
import org.junit.runner.RunWith

@RunWith(KmpAndroidJUnit4::class)
actual abstract class BaseInjectTest actual constructor(
    applicationComponentCreator: (ApplicationComponentArguments) -> ApplicationComponent,
) : BaseInjectTestImpl(applicationComponentCreator) {
    init {
        // If TestInjectApplication is being used, store the created application component into it
        (ApplicationProvider.getApplicationContext<Application>() as? TestInjectApplication)?.applicationComponent =
            this.applicationComponent
    }
}

actual fun createApplicationComponentArguments(): ApplicationComponentArguments =
    object : ApplicationComponentArguments {
        override val application: Application = ApplicationProvider.getApplicationContext()
    }
