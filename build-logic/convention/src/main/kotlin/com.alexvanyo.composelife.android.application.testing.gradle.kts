import com.alexvanyo.composelife.buildlogic.configureTesting
import com.slack.keeper.optInToKeeper

plugins {
    id("com.android.application")
    id("com.slack.keeper")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

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

    dependencies {
        keeperR8(libs.findLibrary("android.r8").get())
    }

    configureTesting(this)
}

keeper {
    automaticR8RepoManagement.set(false)
}
