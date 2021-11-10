package com.alexvanyo.composelife.util

/**
 * An annotation that contains "Generated" to be applied to classes that should be excluded from the JaCoCo report.
 */
@Retention(AnnotationRetention.RUNTIME)
@Target(AnnotationTarget.CLASS)
annotation class ExcludeFromJacocoGeneratedReport
