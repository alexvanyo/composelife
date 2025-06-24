package com.livefront.sealedenum

/**
 * Indicates that an implementation of [SealedEnum] should be generated for the annotated companion object's enclosing
 * sealed class.
 *
 * For example,
 * ```
 * sealed class Alpha {
 *     object Beta : Alpha()
 *     object Gamma : Alpha()
 *
 *     @GenSealedEnum
 *     companion object
 * }
 * ```
 * will generate the following object:
 * ```
 * object AlphaSealedEnum : SealedEnum<Alpha> {
 *     override val values: List<Alpha> by lazy(mode = LazyThreadSafetyMode.PUBLICATION) {
 *         listOf(
 *             Alpha.Beta,
 *             Alpha.Gamma
 *         )
 *     }
 *
 *     override fun ordinalOf(obj: Alpha): Int = when (obj) {
 *         is Alpha.Beta -> 0
 *         is Alpha.Gamma -> 1
 *     }
 *
 *     override fun nameOf(obj: AlphaSealedEnum): String = when (obj) {
 *         is Alpha.Beta -> "Alpha_Beta"
 *         is Alpha.Gamma -> "Alpha_Gamma"
 *     }
 *
 *     override fun valueOf(name: String): AlphaSealedEnum = when (name) {
 *         "Alpha_Beta" -> Alpha.Beta
 *         "Alpha_Gamma" -> Alpha.Gamma
 *         else -> throw IllegalArgumentException("""No sealed enum constant $name""")
 *     }
 * }
 * ```
 *
 * The [SealedEnum.valueOf] and [SealedEnum.nameOf] methods mimic the corresponding [Enum] methods, and use
 * the simple names of the objects joined by underscores.
 *
 * In addition, extension methods on the sealed class and the sealed class's companion object will be generated for
 * convenient access to the generated properties and values:
 *
 * ```
 * val Alpha.ordinal: Int
 *     get() = AlphaSealedEnum.ordinalOf(this)
 *
 * val Alpha.name: String
 *     get() = AlphaSealedEnum.nameOf(this)
 *
 * val Alpha.Companion.values: List<Alpha>
 *     get() = AlphaSealedEnum.values
 *
 * val Alpha.Companion.sealedEnum: AlphaSealedEnum
 *     get() = AlphaSealedEnum
 *
 * fun Alpha.Companion.valueOf(name: String): Alpha = AlphaSealedEnum.valueOf(name)
 * ```
 *
 * If there is a nested hierarchy of sealed classes, then `values` will contain all object subclasses, with the
 * tree ordering given by [traversalOrder].
 * By default, an [TreeTraversalOrder.IN_ORDER] will be used.
 *
 * If multiple ordering strategies are desired simultaneously, then the sealed class's companion object can be annotated
 * with multiple [GenSealedEnum] annotations, with different [TreeTraversalOrder]s.
 * This will cause multiple objects to be generated, with different names to indicate the traversal order used.
 *
 * For example,
 * ```
 * sealed class Alpha {
 *     sealed class Beta : Alpha() {
 *         object Gamma : Beta()
 *     }
 *     object Delta : Alpha()
 *     sealed class Epsilon : Alpha() {
 *         object Zeta : Epsilon()
 *     }
 *
 *     @GenSealedEnum(traversalOrder = TreeTraversalOrder.IN_ORDER)
 *     @GenSealedEnum(traversalOrder = TreeTraversalOrder.LEVEL_ORDER)
 *     companion object
 * }
 * ```
 * will generate two objects:
 * ```
 * object AlphaLevelOrderSealedEnum : SealedEnum<Alpha> {
 *     override val values: List<Alpha> by lazy(mode = LazyThreadSafetyMode.PUBLICATION) {
 *         listOf(
 *             Alpha.Delta,
 *             Alpha.Beta.Gamma,
 *             Alpha.Epsilon.Zeta
 *         )
 *     }
 *
 *     override fun ordinalOf(obj: Alpha): Int = when (obj) {
 *         is Alpha.Delta -> 0
 *         is Alpha.Beta.Gamma -> 1
 *         is Alpha.Epsilon.Zeta -> 2
 *     }
 *
 *     override fun nameOf(obj: AlphaLevelOrderSealedEnum): String = when (obj) {
 *         is Alpha.Delta -> "Alpha_Delta"
 *         is Alpha.Beta.Gamma -> "Alpha_Beta_Gamma"
 *         is Alpha.Epsilon.Zeta -> "Alpha_Epsilon_Zeta"
 *     }
 *
 *     override fun valueOf(name: String): AlphaLevelOrderSealedEnum = when (name) {
 *         "Alpha_Delta" -> Alpha.Delta
 *         "Alpha_Beta_Gamma" -> Alpha.Beta.Gamma
 *         "Alpha_Epsilon_Zeta" -> Alpha.Epsilon.Zeta
 *         else -> throw IllegalArgumentException("""No sealed enum constant $name""")
 *     }
 * }
 *
 * object AlphaInOrderSealedEnum : SealedEnum<Alpha> {
 *     override val values: List<Alpha> by lazy(mode = LazyThreadSafetyMode.PUBLICATION) {
 *         listOf(
 *             Alpha.Beta.Gamma,
 *             Alpha.Delta,
 *             Alpha.Epsilon.Zeta
 *         )
 *     }
 *
 *     override fun ordinalOf(obj: Alpha): Int = when (obj) {
 *         is Alpha.Beta.Gamma -> 0
 *         is Alpha.Delta -> 1
 *         is Alpha.Epsilon.Zeta -> 2
 *     }
 *
 *     override fun nameOf(obj: AlphaInOrderSealedEnum): String = when (obj) {
 *         is Alpha.Beta.Gamma -> "Alpha_Beta_Gamma"
 *         is Alpha.Delta -> "Alpha_Delta"
 *         is Alpha.Epsilon.Zeta -> "Alpha_Epsilon_Zeta"
 *     }
 *
 *     override fun valueOf(name: String): AlphaInOrderSealedEnum = when (name) {
 *         "Alpha_Beta_Gamma" -> Alpha.Beta.Gamma
 *         "Alpha_Delta" -> Alpha.Delta
 *         "Alpha_Epsilon_Zeta" -> Alpha.Epsilon.Zeta
 *         else -> throw IllegalArgumentException("""No sealed enum constant $name""")
 *     }
 * }
 * ```
 *
 * The generated extensions will also be prefixed with the traversal order to disambiguate them:
 *
 * ```
 * val Alpha.levelOrderOrdinal: Int
 *     get() = AlphaLevelOrderSealedEnum.ordinalOf(this)
 *
 * val Alpha.levelOrderName: String
 *     get() = AlphaLevelOrderSealedEnum.nameOf(this)
 *
 * val Alpha.Companion.levelOrderValues: List<Alpha>
 *     get() = AlphaLevelOrderSealedEnum.values
 *
 * val Alpha.Companion.levelOrderSealedEnum: AlphaLevelOrderSealedEnum
 *     get() = AlphaLevelOrderSealedEnum
 *
 * fun Alpha.Companion.levelOrderValueOf(name: String): Alpha = AlphaLevelOrderSealedEnum.valueOf(name)
 *
 * val Alpha.inOrderOrdinal: Int
 *     get() = AlphaInOrderSealedEnum.ordinalOf(this)
 *
 * val Alpha.inOrderName: String
 *     get() = AlphaInOrderSealedEnum.nameOf(this)
 *
 * val Alpha.Companion.inOrderValues: List<Alpha>
 *     get() = AlphaInOrderSealedEnum.values
 *
 * val Alpha.Companion.inOrderSealedEnum: AlphaInOrderSealedEnum
 *     get() = AlphaInOrderSealedEnum
 *
 * fun Alpha.Companion.inOrderValueOf(name: String): Alpha = AlphaInOrderSealedEnum.valueOf(name)
 *
 * ```
 *
 * If the sealed class (or any child sealed class) has non-object and non-sealed subclasses, they will cause
 * annotation processing to fail.
 *
 * If the sealed class has generic type arguments, then the generated object will specify them if they are invariant,
 * otherwise the sealed class type will be star-projected.
 *
 * If [generateEnum] is true, then a normal enum class will be generated that is close to equivalent to the original
 * sealed class. In essence, the enum will implement all interfaces that the sealed class implements, and the objects
 * will be isomorphic to the sealed class objects. To work with the enum, the generated object will implement
 * [EnumForSealedEnumProvider] in addition to [SealedEnum]. This provider has [EnumForSealedEnumProvider.enumClass],
 * which returns the enum's class, and [EnumForSealedEnumProvider.sealedObjectToEnum] and
 * [EnumForSealedEnumProvider.enumToSealedObject] together provide the isomorphism from the sealed objects to
 * enum constants.
 *
 * In addition, the ordinals of the enum constants will match the ordinals for the sealed class objects (as
 * determined by [traversalOrder]), and the names of the sealed objects (as given by [SealedEnum.nameOf] and
 * [SealedEnum.valueOf]) will match the names of the enum constants (assuming no obfuscation occurs).
 */
@RepeatableContainer(GenSealedEnums::class)
@Retention(AnnotationRetention.SOURCE)
@Target(AnnotationTarget.CLASS)
@Repeatable
public annotation class GenSealedEnum(
    val traversalOrder: TreeTraversalOrder = TreeTraversalOrder.IN_ORDER,
    val generateEnum: Boolean = false
)

/**
 * This is the container annotation for multiple [GenSealedEnum] annotations.
 */
@Retention(AnnotationRetention.SOURCE)
@Target(AnnotationTarget.CLASS)
public annotation class GenSealedEnums(vararg val value: GenSealedEnum)
