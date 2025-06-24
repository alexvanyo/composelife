package com.livefront.sealedenum

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.fail

enum class AlphaEnum { BETA, GAMMA, DELTA }

class CreateSealedEnumFromEnumTests {

    private val alphaEnumSealedEnum = createSealedEnumFromEnum<AlphaEnum>()

    @Test
    fun verify_values_are_correct() {
        assertEquals(listOf(AlphaEnum.BETA, AlphaEnum.GAMMA, AlphaEnum.DELTA), alphaEnumSealedEnum.values)
    }

    @Test
    fun verify_ordinal_of_BETA_is_correct() {
        assertEquals(0, alphaEnumSealedEnum.ordinalOf(AlphaEnum.BETA))
    }

    @Test
    fun verify_ordinal_of_GAMMA_is_correct() {
        assertEquals(1, alphaEnumSealedEnum.ordinalOf(AlphaEnum.GAMMA))
    }

    @Test
    fun verify_ordinal_of_DELTA_is_correct() {
        assertEquals(2, alphaEnumSealedEnum.ordinalOf(AlphaEnum.DELTA))
    }

    data class ComparatorConfig(
        val first: AlphaEnum,
        val second: AlphaEnum,
        val compareValue: Int
    )

    @Test
    fun verify_compareTo_is_correct() {
        listOf(
            ComparatorConfig(AlphaEnum.BETA, AlphaEnum.BETA, 0),
            ComparatorConfig(AlphaEnum.BETA, AlphaEnum.GAMMA, -1),
            ComparatorConfig(AlphaEnum.BETA, AlphaEnum.DELTA, -2),
            ComparatorConfig(AlphaEnum.GAMMA, AlphaEnum.BETA, 1),
            ComparatorConfig(AlphaEnum.GAMMA, AlphaEnum.GAMMA, 0),
            ComparatorConfig(AlphaEnum.GAMMA, AlphaEnum.DELTA, -1),
            ComparatorConfig(AlphaEnum.DELTA, AlphaEnum.BETA, 2),
            ComparatorConfig(AlphaEnum.DELTA, AlphaEnum.GAMMA, 1),
            ComparatorConfig(AlphaEnum.DELTA, AlphaEnum.DELTA, 0)
        ).forEach { config ->
            assertEquals(config.compareValue, alphaEnumSealedEnum.compare(config.first, config.second))
        }
    }

    @Test
    fun verify_name_of_BETA_is_correct() {
        assertEquals("BETA", alphaEnumSealedEnum.nameOf(AlphaEnum.BETA))
    }

    @Test
    fun verify_name_of_GAMMA_is_correct() {
        assertEquals("GAMMA", alphaEnumSealedEnum.nameOf(AlphaEnum.GAMMA))
    }

    @Test
    fun verify_name_of_DELTA_is_correct() {
        assertEquals("DELTA", alphaEnumSealedEnum.nameOf(AlphaEnum.DELTA))
    }

    @Test
    fun verify_valueOf_of_BETA_is_correct() {
        assertEquals(AlphaEnum.BETA, alphaEnumSealedEnum.valueOf("BETA"))
    }

    @Test
    fun verify_valueOf_of_GAMMA_is_correct() {
        assertEquals(AlphaEnum.GAMMA, alphaEnumSealedEnum.valueOf("GAMMA"))
    }

    @Test
    fun verify_valueOf_of_DELTA_is_correct() {
        assertEquals(AlphaEnum.DELTA, alphaEnumSealedEnum.valueOf("DELTA"))
    }

    @Test
    fun verify_valueOf_of_EPSILON_throws_exception() {
        try {
            alphaEnumSealedEnum.valueOf("EPSILON")
            fail()
        } catch (exception: IllegalArgumentException) {
            // expected to throw
        }
    }

    @Test
    fun verify_enum_class_is_correct() {
        assertEquals(AlphaEnum::class, alphaEnumSealedEnum.enumClass)
    }

    @Test
    fun verify_sealed_enum_to_object_is_correct_for_BETA() {
        assertEquals(AlphaEnum.BETA, alphaEnumSealedEnum.sealedObjectToEnum(AlphaEnum.BETA))
    }

    @Test
    fun verify_sealed_enum_to_object_is_correct_for_GAMMA() {
        assertEquals(AlphaEnum.GAMMA, alphaEnumSealedEnum.sealedObjectToEnum(AlphaEnum.GAMMA))
    }

    @Test
    fun verify_sealed_enum_to_object_is_correct_for_DELTA() {
        assertEquals(AlphaEnum.DELTA, alphaEnumSealedEnum.sealedObjectToEnum(AlphaEnum.DELTA))
    }

    @Test
    fun verify_object_to_sealed_enum_is_correct_for_BETA() {
        assertEquals(AlphaEnum.BETA, alphaEnumSealedEnum.enumToSealedObject(AlphaEnum.BETA))
    }

    @Test
    fun verify_object_to_sealed_enum_is_correct_for_GAMMA() {
        assertEquals(AlphaEnum.GAMMA, alphaEnumSealedEnum.enumToSealedObject(AlphaEnum.GAMMA))
    }

    @Test
    fun verify_object_to_sealed_enum_is_correct_for_DELTA() {
        assertEquals(AlphaEnum.DELTA, alphaEnumSealedEnum.enumToSealedObject(AlphaEnum.DELTA))
    }
}
