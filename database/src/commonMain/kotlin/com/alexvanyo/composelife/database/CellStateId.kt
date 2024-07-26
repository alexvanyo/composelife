/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.database

import app.cash.sqldelight.ColumnAdapter
import me.tatarka.inject.annotations.Inject
import kotlin.jvm.JvmInline

@JvmInline
value class CellStateId(val value: Long)

@Inject
class CellStateIdAdapter : ColumnAdapter<CellStateId, Long> {
    override fun decode(databaseValue: Long): CellStateId = CellStateId(databaseValue)

    override fun encode(value: CellStateId): Long = value.value
}
