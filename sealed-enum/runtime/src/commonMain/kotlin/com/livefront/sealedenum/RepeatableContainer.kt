package com.livefront.sealedenum

import kotlin.reflect.KClass

/**
 * A multiplatform expectation for the Java Repeatable annotation.
 */
@OptIn(ExperimentalMultiplatform::class)
@OptionalExpectation
public expect annotation class RepeatableContainer(val value: KClass<out Annotation>)
