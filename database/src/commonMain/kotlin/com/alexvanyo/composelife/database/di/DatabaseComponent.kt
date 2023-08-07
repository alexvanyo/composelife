package com.alexvanyo.composelife.database.di

import app.cash.sqldelight.db.SqlDriver
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.scopes.Singleton
import me.tatarka.inject.annotations.Provides

interface DatabaseComponent : DatabaseModule, AdapterComponent, DriverComponent, QueriesComponent {

    @Provides
    @Singleton
    fun providesDatabase(
        driver: SqlDriver,
        cellStateAdapter: CellState.Adapter,
    ): ComposeLifeDatabase =
        ComposeLifeDatabase(
            driver = driver,
            cellStateAdapter = cellStateAdapter,
        )
}
