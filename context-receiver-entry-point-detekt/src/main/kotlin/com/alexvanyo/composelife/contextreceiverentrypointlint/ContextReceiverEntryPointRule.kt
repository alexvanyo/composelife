/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.contextreceiverentrypointlint

import io.gitlab.arturbosch.detekt.api.CodeSmell
import io.gitlab.arturbosch.detekt.api.Config
import io.gitlab.arturbosch.detekt.api.Debt
import io.gitlab.arturbosch.detekt.api.Entity
import io.gitlab.arturbosch.detekt.api.Issue
import io.gitlab.arturbosch.detekt.api.Rule
import io.gitlab.arturbosch.detekt.api.Severity
import io.gitlab.arturbosch.detekt.api.internal.RequiresTypeResolution
import io.gitlab.arturbosch.detekt.rules.fqNameOrNull
import org.jetbrains.kotlin.fir.builder.toUnaryName
import org.jetbrains.kotlin.idea.references.mainReference
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.psi.KtNameReferenceExpression
import org.jetbrains.kotlin.psi.KtNamedFunction
import org.jetbrains.kotlin.psi.KtSimpleNameExpression
import org.jetbrains.kotlin.psi.KtVisitorVoid
import org.jetbrains.kotlin.psi.psiUtil.forEachDescendantOfType
import org.jetbrains.kotlin.psi.psiUtil.getQualifiedExpressionForReceiver
import org.jetbrains.kotlin.psi.psiUtil.getQualifiedExpressionForSelector
import org.jetbrains.kotlin.psi.psiUtil.isContextualDeclaration
import org.jetbrains.kotlin.psi.psiUtil.referenceExpression
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.bindingContextUtil.getReferenceTargets
import org.jetbrains.kotlin.resolve.calls.inference.toHandle
import org.jetbrains.kotlin.resolve.calls.util.getCall
import org.jetbrains.kotlin.resolve.calls.util.getDispatchReceiverWithSmartCast
import org.jetbrains.kotlin.resolve.calls.util.getParentResolvedCall
import org.jetbrains.kotlin.resolve.calls.util.getResolvedCall
import org.jetbrains.kotlin.resolve.calls.util.getType
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameOrNull
import org.jetbrains.kotlin.resolve.scopes.receivers.ExpressionReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ImplicitReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.QualifierReceiver
import org.jetbrains.kotlin.resolve.scopes.receivers.ThisClassReceiver
import org.jetbrains.kotlin.types.checker.SimpleClassicTypeSystemContext.hasAnnotation
import org.jetbrains.kotlin.types.typeUtil.supertypes

@RequiresTypeResolution
class ContextReceiverEntryPointRule(
    config: Config = Config.empty
) : Rule(config) {

    override val issue = Issue(
        "ContextReceiverEntryPoint",
        Severity.Maintainability,
        "A member available in the scope of an entry point was used implicitly",
        Debt.FIVE_MINS,
    )

    override fun visitNamedFunction(function: KtNamedFunction) {
        val contextReceiverEntryPointFqn =
            FqName("com.alexvanyo.composelife.contextreceiverentrypoint.ContextReceiverEntryPoint")

        val contextReceiverEntryPointTypes = function.contextReceivers
            .mapNotNull { contextReceiver ->
                bindingContext[BindingContext.TYPE, contextReceiver.typeReference()]
            }
            .filter { contextReceiverType ->
                contextReceiverType.hasAnnotation(contextReceiverEntryPointFqn)
            }
            .flatMap { contextReceiverType ->
                contextReceiverType.supertypes() + contextReceiverType
            }

        function.bodyBlockExpression?.forEachDescendantOfType<KtNameReferenceExpression> { expression ->
            val containingDeclaration = expression.getQualifiedExpressionForReceiver()
            containingDeclaration

            if (
                containingDeclaration != null
            ) {
                report(
                    CodeSmell(
                        issue,
                        Entity.from(expression),
                        "Expression ${(containingDeclaration.getCall(bindingContext)?.explicitReceiver as? ExpressionReceiver)?.type?.constructor?.declarationDescriptor?.source?.containingFile?.name } is used implicitly"
                    )
                )
            }

//            if (
//                containingDeclaration != null &&
//                containingDeclaration.annotations.hasAnnotation(contextReceiverEntryPointFqn) &&
//                containingDeclaration.fqNameOrNull() !in contextReceiverEntryPointTypes.map {
//                    it.fqNameOrNull()
//                }
//            ) {
//                report(
//                    CodeSmell(
//                        issue,
//                        Entity.from(expression),
//                        "Expression ${expression.name} is used implicitly"
//                    )
//                )
//            }
        }
    }
}
