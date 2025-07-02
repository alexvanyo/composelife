package com.livefront.sealedenum

/**
 * A [SealedEnum] along with a [EnumForSealedEnumProvider].
 */
public interface SealedEnumWithEnumProvider<T, E : Enum<E>> : SealedEnum<T>, EnumForSealedEnumProvider<T, E>
