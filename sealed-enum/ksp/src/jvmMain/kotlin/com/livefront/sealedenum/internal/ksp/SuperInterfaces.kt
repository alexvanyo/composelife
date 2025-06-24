package com.livefront.sealedenum.internal.ksp

import com.google.devtools.ksp.isInternal
import com.google.devtools.ksp.isJavaPackagePrivate
import com.google.devtools.ksp.isProtected
import com.google.devtools.ksp.isPublic
import com.google.devtools.ksp.symbol.ClassKind
import com.google.devtools.ksp.symbol.KSClassDeclaration
import com.google.devtools.ksp.symbol.KSType
import com.google.devtools.ksp.symbol.KSTypeParameter
import com.google.devtools.ksp.symbol.Modifier
import com.google.devtools.ksp.symbol.Origin
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.ParameterizedTypeName
import com.squareup.kotlinpoet.STAR
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.WildcardTypeName

/**
 * An internal context with which super interfaces can be determined.
 */
internal class SuperInterfaces(
    private val sealedEnumKSClass: KSClassDeclaration
) {

    /**
     * Returns a list of all valid super interfaces that it or any of its superclasses implement.
     *
     * A super interface is "valid" if it does not require a wildcard generic type parameter and if it is of an
     * appropriate visibility.
     */
    fun getAllSuperInterfaces(): List<TypeName> {
        val superInterfaces = mutableListOf<TypeName>()

        getAllSuperInterfacesImpl(
            sealedEnumKSClass,
            sealedEnumKSClass.wildcardedTypeNames(),
            superInterfaces
        )

        return superInterfaces
    }

    /**
     * The recursive implementation for [getAllSuperInterfaces].
     *
     * This method adds all valid super interfaces to [superInterfaces].
     */
    private tailrec fun getAllSuperInterfacesImpl(
        sealedEnumKSClass: KSClassDeclaration,
        parentTypeArguments: List<TypeName>,
        superInterfaces: MutableList<TypeName>,
    ) {
        check(sealedEnumKSClass.typeParameters.size == parentTypeArguments.size)

        // Associate the type variable names with their type arguments from the subclass.
        val typeVariableNamesToTypeArguments = sealedEnumKSClass.typeParameters
            .map { it.name.asString() }.zip(parentTypeArguments).toMap()

        // Add all implement interfaces to our list, taking care to substitute the type names and throwing away invalid
        // interfaces
        superInterfaces += sealedEnumKSClass.superTypes
            .asSequence()
            .map { it.resolve() }
            .filter {
                val declaration = it.declaration
                declaration is KSClassDeclaration &&
                    declaration.classKind == ClassKind.INTERFACE &&
                    declaration.isVisibleInterface() &&
                    !declaration.isSealedInterface()
            }
            .map { it.substituteTypeNames(typeVariableNamesToTypeArguments) }
            .filter { it.isValidInterface() }

        val superClassKSType = sealedEnumKSClass.superTypes.firstOrNull()?.resolve() ?: return
        val superClassKSDeclaration = superClassKSType.declaration as? KSClassDeclaration ?: return

        getAllSuperInterfacesImpl(
            superClassKSDeclaration,
            superClassKSType.arguments
                .mapNotNull { it.type }
                .map { it.resolve() }
                .map { it.substituteTypeNames(typeVariableNamesToTypeArguments) },
            superInterfaces
        )
    }

    private fun KSType.substituteTypeNames(typeVariableNamesToTypeArguments: Map<String, TypeName>): TypeName =
        when (val declaration = this.declaration) {
            is KSClassDeclaration -> declaration.toTypeName(
                arguments
                    .mapNotNull { it.type }
                    .map { it.resolve() }
                    .map { it.substituteTypeNames(typeVariableNamesToTypeArguments) }
            ).copy(nullable = isMarkedNullable)
            is KSTypeParameter -> typeVariableNamesToTypeArguments[declaration.name.asString()] ?: STAR
            else -> STAR
        }

    /**
     * Returns true if the [KSClassDeclaration] interface has the correct visibility to be implemented by a generated
     * enum.
     */
    private fun KSClassDeclaration.isVisibleInterface(): Boolean =
        isPublic() || isInternal() || isJavaPackagePrivate() ||
            (isProtected() && origin == Origin.JAVA && packageName == sealedEnumKSClass.packageName)

    /**
     * Returns true if the [KSClassDeclaration] interface is sealed.
     */
    private fun KSClassDeclaration.isSealedInterface(): Boolean =
        modifiers.contains(Modifier.SEALED)

    /**
     * Returns true if the [TypeName] interface has the correct parameterization (if any) to be implemented by a
     * generated enum.
     */
    private fun TypeName.isValidInterface(): Boolean = when (this) {
        is ClassName -> true
        is ParameterizedTypeName -> typeArguments.none { it is WildcardTypeName }
        else -> false
    }
}
