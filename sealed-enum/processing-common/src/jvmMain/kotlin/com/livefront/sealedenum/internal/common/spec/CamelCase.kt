package com.livefront.sealedenum.internal.common.spec

/**
 * Converts a PascalCase string to a camelCase string. That is, this function lowercases the first letter.
 *
 * This function assumes that [pascalCase] is non-empty.
 */
internal fun pascalCaseToCamelCase(pascalCase: String): String =
    pascalCase.take(1).lowercase() + pascalCase.drop(1)
