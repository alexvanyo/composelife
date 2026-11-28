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

package com.alexvanyo.composelife.wear

import com.alexvanyo.composelife.BaseComposeLifeApplication
import com.alexvanyo.composelife.ComposeLifeApplicationCtx
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.ApplicationGraphArguments
import com.alexvanyo.composelife.tracing.Tracer
import com.alexvanyo.composelife.wear.watchface.GameOfLifeWatchFaceServiceCtx
import com.alexvanyo.composelife.wear.watchface.GameOfLifeWatchFaceServiceCtxOwner
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.asContribution
import dev.zacsweers.metro.createGraphFactory

class ComposeLifeApplication :
    BaseComposeLifeApplication<WearApplicationGraph>({ tracer, applicationGraphArguments ->
        createGraphFactory<WearApplicationGraph.Factory>().create(
            tracer = tracer,
            applicationGraphArguments = applicationGraphArguments,
        )
    }),
    GameOfLifeWatchFaceServiceCtxOwner {
    override val gameOfLifeWatchFaceServiceCtx: GameOfLifeWatchFaceServiceCtx
        get() = applicationGraph.asContribution<GameOfLifeWatchFaceServiceCtx>()
}

@DependencyGraph(AppScope::class)
interface WearApplicationGraph :
    ApplicationGraph,
    ComposeLifeApplicationCtx {
    @DependencyGraph.Factory
    fun interface Factory {
        fun create(
            @Provides tracer: Tracer,
            @Provides applicationGraphArguments: ApplicationGraphArguments,
        ): WearApplicationGraph
    }
}
