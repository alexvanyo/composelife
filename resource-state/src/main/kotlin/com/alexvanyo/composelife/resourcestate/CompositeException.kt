package com.alexvanyo.composelife.resourcestate

/**
 * An exception caused by a combination of the given [exceptions].
 *
 * Note that [exceptions] should not be empty (since there would be no exception) and [exceptions] should not only
 * contain one exception (prefer to just throw that instead.
 */
class CompositeException(
    val exceptions: List<Throwable>
) : RuntimeException() {
    constructor(
        vararg exceptions: Throwable
    ) : this(exceptions.toList())

    init {
        require(exceptions.size >= 2)
    }

    override val message: String = "${exceptions.size} exceptions occurred."

    override val cause: Throwable
        get() = exceptions.first()
}
