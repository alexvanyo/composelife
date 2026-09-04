/*
 * Copyright 2026 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.di

import org.jetbrains.kotlin.GeneratedDeclarationKey
import org.jetbrains.kotlin.KtSourceElement
import org.jetbrains.kotlin.descriptors.EffectiveVisibility
import org.jetbrains.kotlin.descriptors.Modality
import org.jetbrains.kotlin.descriptors.Visibilities
import org.jetbrains.kotlin.descriptors.annotations.AnnotationUseSiteTarget
import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.declarations.FirDeclarationOrigin
import org.jetbrains.kotlin.fir.declarations.FirResolvePhase
import org.jetbrains.kotlin.fir.declarations.FirValueParameter
import org.jetbrains.kotlin.fir.declarations.FirValueParameterKind
import org.jetbrains.kotlin.fir.declarations.builder.buildNamedFunction
import org.jetbrains.kotlin.fir.declarations.builder.buildValueParameter
import org.jetbrains.kotlin.fir.declarations.getAnnotationByClassId
import org.jetbrains.kotlin.fir.declarations.impl.FirResolvedDeclarationStatusImpl
import org.jetbrains.kotlin.fir.expressions.FirAnnotation
import org.jetbrains.kotlin.fir.expressions.FirAnnotationArgumentMapping
import org.jetbrains.kotlin.fir.expressions.FirAnnotationCall
import org.jetbrains.kotlin.fir.expressions.FirAnnotationResolvePhase
import org.jetbrains.kotlin.fir.expressions.FirArgumentList
import org.jetbrains.kotlin.fir.expressions.FirEmptyArgumentList
import org.jetbrains.kotlin.fir.expressions.UnresolvedExpressionTypeAccess
import org.jetbrains.kotlin.fir.expressions.builder.buildAnnotationCallCopy
import org.jetbrains.kotlin.fir.extensions.DeclarationGenerationContext
import org.jetbrains.kotlin.fir.extensions.ExperimentalTopLevelDeclarationsGenerationApi
import org.jetbrains.kotlin.fir.extensions.FirDeclarationGenerationExtension
import org.jetbrains.kotlin.fir.extensions.FirDeclarationPredicateRegistrar
import org.jetbrains.kotlin.fir.extensions.FirExtensionRegistrar
import org.jetbrains.kotlin.fir.extensions.predicate.LookupPredicate
import org.jetbrains.kotlin.fir.extensions.predicateBasedProvider
import org.jetbrains.kotlin.fir.moduleData
import org.jetbrains.kotlin.fir.references.FirReference
import org.jetbrains.kotlin.fir.symbols.FirBasedSymbol
import org.jetbrains.kotlin.fir.symbols.SymbolInternals
import org.jetbrains.kotlin.fir.symbols.impl.FirClassLikeSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirClassSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirConstructorSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirNamedFunctionSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirPropertySymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirValueParameterSymbol
import org.jetbrains.kotlin.fir.types.ConeKotlinType
import org.jetbrains.kotlin.fir.types.FirTypeProjection
import org.jetbrains.kotlin.fir.types.FirTypeRef
import org.jetbrains.kotlin.fir.types.builder.buildResolvedTypeRef
import org.jetbrains.kotlin.fir.types.classId
import org.jetbrains.kotlin.fir.types.coneType
import org.jetbrains.kotlin.fir.types.constructClassLikeType
import org.jetbrains.kotlin.fir.visitors.FirTransformer
import org.jetbrains.kotlin.fir.visitors.FirVisitor
import org.jetbrains.kotlin.name.CallableId
import org.jetbrains.kotlin.name.ClassId
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import java.util.concurrent.ConcurrentHashMap

class InjectContextFir : FirExtensionRegistrar() {
    override fun ExtensionRegistrarContext.configurePlugin() {
        +::InjectContextFirExtension
    }
}

@Suppress("LongMethod", "ReturnCount", "UnreachableCode")
@OptIn(ExperimentalTopLevelDeclarationsGenerationApi::class, SymbolInternals::class)
class InjectContextFirExtension(session: FirSession) : FirDeclarationGenerationExtension(session) {
    companion object {
        val injectContextPredicate: LookupPredicate = LookupPredicate.create {
            annotated(FqName("com.alexvanyo.composelife.di.InjectContext"))
        }
    }

    private val functionSymbols = ConcurrentHashMap<CallableId, List<FirNamedFunctionSymbol>>()

    private val annotatedFunctions: List<FirNamedFunctionSymbol>
        get() = session.predicateBasedProvider
            .getSymbolsByPredicate(injectContextPredicate)
            .filterIsInstance<FirNamedFunctionSymbol>()
            .toList()

    override fun FirDeclarationPredicateRegistrar.registerPredicates() {
        register(injectContextPredicate)
    }

    override fun hasPackage(packageFqName: FqName): Boolean = annotatedFunctions.any {
        it.callableId.packageName == packageFqName
    }

    override fun getTopLevelCallableIds(): Set<CallableId> = annotatedFunctions.mapTo(mutableSetOf()) { it.callableId }

    override fun getTopLevelClassIds(): Set<ClassId> = emptySet()

    override fun generateTopLevelClassLikeDeclaration(classId: ClassId): FirClassLikeSymbol<*>? = null

    override fun getCallableNamesForClass(
        classSymbol: FirClassSymbol<*>,
        context: DeclarationGenerationContext.Member,
    ): Set<Name> = emptySet()

    override fun generateProperties(
        callableId: CallableId,
        context: DeclarationGenerationContext.Member?,
    ): List<FirPropertySymbol> = emptyList()

    override fun generateConstructors(context: DeclarationGenerationContext.Member): List<FirConstructorSymbol> =
        emptyList()

    @Suppress("CyclomaticComplexMethod", "LongMethod")
    override fun generateFunctions(
        callableId: CallableId,
        context: DeclarationGenerationContext.Member?,
    ): List<FirNamedFunctionSymbol> {
        val classId = callableId.classId
        if (classId != null) {
            return emptyList()
        }

        // Top-level function generation
        val originalFunctions = annotatedFunctions.filter { it.callableId == callableId }
        if (originalFunctions.isEmpty()) return emptyList()

        return functionSymbols.getOrPut(callableId) {
            originalFunctions.flatMap { originalFunction ->
                val functionName = originalFunction.name
                val functionClassId = ClassId(
                    originalFunction.callableId.packageName,
                    functionName,
                )

                val assistedClassId = ClassId(
                    FqName("dev.zacsweers.metro"),
                    Name.identifier("Assisted"),
                )
                val injectContextClassId = ClassId(
                    FqName("com.alexvanyo.composelife.di"),
                    Name.identifier("InjectContext"),
                )
                val injectClassId = ClassId(
                    FqName("dev.zacsweers.metro"),
                    Name.identifier("Inject"),
                )

                val assistedParameters = originalFunction.fir.valueParameters.filter {
                    it.getAnnotationByClassId(assistedClassId, session) != null
                }
                val hasDefaultAssisted = assistedParameters.any { it.defaultValue != null }

                val list = mutableListOf<FirNamedFunctionSymbol>()

                val symbol1 = FirNamedFunctionSymbol(callableId)
                buildNamedFunction {
                    resolvePhase = FirResolvePhase.BODY_RESOLVE
                    isLocal = false
                    moduleData = session.moduleData
                    origin = FirDeclarationOrigin.Plugin(Key)
                    name = functionName
                    symbol = symbol1
                    status = FirResolvedDeclarationStatusImpl(
                        Visibilities.Public,
                        Modality.FINAL,
                        EffectiveVisibility.Public,
                    )
                    returnTypeRef = buildResolvedTypeRef {
                        coneType = originalFunction.fir.returnTypeRef.coneType
                    }

                    assistedParameters.forEach { parameter ->
                        valueParameters += buildValueParameter {
                            resolvePhase = FirResolvePhase.BODY_RESOLVE
                            moduleData = session.moduleData
                            origin = FirDeclarationOrigin.Plugin(Key)
                            containingDeclarationSymbol = symbol1
                            name = parameter.name
                            symbol = FirValueParameterSymbol()
                            returnTypeRef = buildResolvedTypeRef {
                                coneType = parameter.returnTypeRef.coneType
                            }
                            valueParameterKind = FirValueParameterKind.Regular
                        }
                    }

                    contextParameters += buildValueParameter {
                        resolvePhase = FirResolvePhase.BODY_RESOLVE
                        moduleData = session.moduleData
                        origin = FirDeclarationOrigin.Plugin(Key)
                        containingDeclarationSymbol = symbol1
                        name = Name.identifier("ctx")
                        symbol = FirValueParameterSymbol()
                        returnTypeRef = buildResolvedTypeRef {
                            coneType = functionClassId.constructClassLikeType()
                        }
                        valueParameterKind = FirValueParameterKind.ContextParameter
                    }

                    annotations += originalFunction.fir.annotations.filter {
                        val cid = it.annotationTypeRef.coneType.classId
                        cid != injectContextClassId && cid != injectClassId
                    }.filterIsInstance<FirAnnotationCall>().map { annotation ->
                        DelegatingAnnotationCall(
                            buildAnnotationCallCopy(annotation) {
                                containingDeclarationSymbol = symbol1
                                argumentList = FirEmptyArgumentList
                            },
                        )
                    }
                }.also { list += it.symbol }

                if (hasDefaultAssisted) {
                    val defaultedParameters = assistedParameters.filter { it.defaultValue != null }

                    var subsets = listOf(emptyList<FirValueParameter>())
                    for (param in defaultedParameters) {
                        subsets = subsets + subsets.map { it + param }
                    }

                    for (subset in subsets) {
                        if (subset.size == defaultedParameters.size) continue
                        val subsetSet = subset.toSet()
                        val currentParameters = assistedParameters.filter { it.defaultValue == null || it in subsetSet }
                        val symbolOverload = FirNamedFunctionSymbol(callableId)
                        buildNamedFunction {
                            resolvePhase = FirResolvePhase.BODY_RESOLVE
                            isLocal = false
                            moduleData = session.moduleData
                            origin = FirDeclarationOrigin.Plugin(Key)
                            name = functionName
                            symbol = symbolOverload
                            status = FirResolvedDeclarationStatusImpl(
                                Visibilities.Public,
                                Modality.FINAL,
                                EffectiveVisibility.Public,
                            )
                            returnTypeRef = buildResolvedTypeRef {
                                coneType = originalFunction.fir.returnTypeRef.coneType
                            }

                            currentParameters.forEach { parameter ->
                                valueParameters += buildValueParameter {
                                    resolvePhase = FirResolvePhase.BODY_RESOLVE
                                    moduleData = session.moduleData
                                    origin = FirDeclarationOrigin.Plugin(Key)
                                    containingDeclarationSymbol = symbolOverload
                                    name = parameter.name
                                    symbol = FirValueParameterSymbol()
                                    returnTypeRef = buildResolvedTypeRef {
                                        coneType = parameter.returnTypeRef.coneType
                                    }
                                    valueParameterKind = FirValueParameterKind.Regular
                                }
                            }

                            contextParameters += buildValueParameter {
                                resolvePhase = FirResolvePhase.BODY_RESOLVE
                                moduleData = session.moduleData
                                origin = FirDeclarationOrigin.Plugin(Key)
                                containingDeclarationSymbol = symbolOverload
                                name = Name.identifier("ctx")
                                symbol = FirValueParameterSymbol()
                                returnTypeRef = buildResolvedTypeRef {
                                    coneType = functionClassId.constructClassLikeType()
                                }
                                valueParameterKind = FirValueParameterKind.ContextParameter
                            }

                            annotations += originalFunction.fir.annotations.filter {
                                val cid = it.annotationTypeRef.coneType.classId
                                cid != injectContextClassId && cid != injectClassId
                            }.filterIsInstance<FirAnnotationCall>().map { annotation ->
                                DelegatingAnnotationCall(
                                    buildAnnotationCallCopy(annotation) {
                                        containingDeclarationSymbol = symbolOverload
                                        argumentList = FirEmptyArgumentList
                                    },
                                )
                            }
                        }.also { list += it.symbol }
                    }
                }

                list
            }
        }
    }

    object Key : GeneratedDeclarationKey()
}

@Suppress("TooManyFunctions")
@OptIn(UnresolvedExpressionTypeAccess::class)
class DelegatingAnnotationCall(private val delegate: FirAnnotationCall) : FirAnnotationCall() {
    override val argumentList: FirArgumentList
        get() = delegate.argumentList

    override val useSiteTarget: AnnotationUseSiteTarget?
        get() = delegate.useSiteTarget

    override val containingDeclarationSymbol: FirBasedSymbol<*>
        get() = delegate.containingDeclarationSymbol

    override val annotationResolvePhase: FirAnnotationResolvePhase
        get() = delegate.annotationResolvePhase

    override val annotationTypeRef: FirTypeRef
        get() = delegate.annotationTypeRef

    override val argumentMapping: FirAnnotationArgumentMapping
        get() = delegate.argumentMapping

    override val calleeReference: FirReference
        get() = delegate.calleeReference

    @UnresolvedExpressionTypeAccess
    override val coneTypeOrNull: ConeKotlinType?
        get() = delegate.coneTypeOrNull

    override fun replaceAnnotationResolvePhase(newAnnotationResolvePhase: FirAnnotationResolvePhase) {
        delegate.replaceAnnotationResolvePhase(newAnnotationResolvePhase)
    }

    override fun replaceAnnotationTypeRef(newAnnotationTypeRef: FirTypeRef) {
        delegate.replaceAnnotationTypeRef(newAnnotationTypeRef)
    }

    override fun replaceArgumentList(newArgumentList: FirArgumentList) {
        delegate.replaceArgumentList(newArgumentList)
    }

    override fun replaceArgumentMapping(newArgumentMapping: FirAnnotationArgumentMapping) {
        delegate.replaceArgumentMapping(newArgumentMapping)
    }

    override fun replaceCalleeReference(newCalleeReference: FirReference) {
        delegate.replaceCalleeReference(newCalleeReference)
    }

    @UnresolvedExpressionTypeAccess
    override fun replaceConeTypeOrNull(newConeTypeOrNull: ConeKotlinType?) {
        delegate.replaceConeTypeOrNull(newConeTypeOrNull)
    }

    override fun replaceTypeArguments(newTypeArguments: List<FirTypeProjection>) {
        delegate.replaceTypeArguments(newTypeArguments)
    }

    override fun replaceUseSiteTarget(newUseSiteTarget: AnnotationUseSiteTarget?) {
        delegate.replaceUseSiteTarget(newUseSiteTarget)
    }

    override fun <D> transformAnnotationTypeRef(transformer: FirTransformer<D>, data: D): FirAnnotationCall =
        delegate.transformAnnotationTypeRef(transformer, data)

    override fun <D> transformCalleeReference(transformer: FirTransformer<D>, data: D): FirAnnotationCall =
        delegate.transformCalleeReference(transformer, data)

    override fun <D> transformTypeArguments(transformer: FirTransformer<D>, data: D): FirAnnotationCall =
        delegate.transformTypeArguments(transformer, data)

    override val annotations: List<FirAnnotation>
        get() = delegate.annotations

    override val source: KtSourceElement?
        get() = null

    override val typeArguments: List<FirTypeProjection>
        get() = delegate.typeArguments

    override fun replaceAnnotations(newAnnotations: List<FirAnnotation>) {
        delegate.replaceAnnotations(newAnnotations)
    }

    override fun <D> transformAnnotations(transformer: FirTransformer<D>, data: D): FirAnnotationCall =
        delegate.transformAnnotations(transformer, data)

    override fun <R, D> accept(visitor: FirVisitor<R, D>, data: D): R = visitor.visitAnnotationCall(this, data)

    override fun <R, D> acceptChildren(visitor: FirVisitor<R, D>, data: D) {
        // Do not visit children to bypass validation errors on arguments and references
    }

    override fun <D> transformChildren(transformer: FirTransformer<D>, data: D): FirAnnotationCall = this
}
