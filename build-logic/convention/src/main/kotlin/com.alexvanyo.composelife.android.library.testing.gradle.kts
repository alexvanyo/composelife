import com.alexvanyo.composelife.buildlogic.configureTesting

plugins {
    id("com.android.library")
}

android {
    configureTesting(this)
}

fun DependencyHandlerScope.sharedTestImplementation(dependencyNotation: Any) {
    testImplementation(dependencyNotation)

    androidTestImplementation(dependencyNotation)
}
