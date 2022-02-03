import com.alexvanyo.composelife.buildlogic.configureTesting
import com.slack.keeper.optInToKeeper

plugins {
    id("com.android.application")
    id("com.slack.keeper")
}

android {
    defaultConfig {
        testBuildType = "staging"
    }

    androidComponents {
        beforeVariants { builder ->
            if (builder.buildType == "staging") {
                builder.optInToKeeper()
            }
        }
    }

    configureTesting(this)
}

keeper {
    automaticR8RepoManagement.set(false)
}
