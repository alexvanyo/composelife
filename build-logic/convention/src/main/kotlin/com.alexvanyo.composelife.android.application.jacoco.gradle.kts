import com.alexvanyo.composelife.buildlogic.configureJacoco

plugins {
    id("com.android.application")
    jacoco
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

val jacocoTestReport = tasks.create("jacocoTestReport")

android {
    androidComponents {
        configureJacoco(this, jacocoTestReport)
    }
}

jacoco {
    toolVersion = libs.findVersion("jacoco").get().toString()
}

tasks {
    withType<Test> {
        configure<JacocoTaskExtension> {
            // Required for JaCoCo + Robolectric
            // https://github.com/robolectric/robolectric/issues/2230
            isIncludeNoLocationClasses = true

            // Required for JDK 11 with the above
            // https://github.com/gradle/gradle/issues/5184#issuecomment-391982009
            excludes = listOf("jdk.internal.*")
        }
    }
}
