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

import com.android.tools.lint.client.api.UElementHandler
import com.android.tools.lint.detector.api.Category
import com.android.tools.lint.detector.api.Detector
import com.android.tools.lint.detector.api.Implementation
import com.android.tools.lint.detector.api.Issue
import com.android.tools.lint.detector.api.JavaContext
import com.android.tools.lint.detector.api.Scope
import com.android.tools.lint.detector.api.Severity
import com.android.tools.lint.detector.api.SourceCodeScanner
import com.android.tools.lint.detector.api.UastLintUtils.Companion.tryResolveUDeclaration
import com.android.tools.lint.detector.api.getReceiver
import com.intellij.psi.PsiClass
import org.jetbrains.uast.UCallExpression
import org.jetbrains.uast.UCallableReferenceExpression
import org.jetbrains.uast.UElement
import org.jetbrains.uast.UExpression
import org.jetbrains.uast.UField
import org.jetbrains.uast.UMethod
import org.jetbrains.uast.UQualifiedReferenceExpression
import org.jetbrains.uast.USimpleNameReferenceExpression
import org.jetbrains.uast.UVariable
import org.jetbrains.uast.getContainingDeclaration
import org.jetbrains.uast.getContainingUClass
import org.jetbrains.uast.resolveToUElement
import org.jetbrains.uast.visitor.AbstractUastVisitor

class ContextReceiverEntryPointDetector : Detector(), SourceCodeScanner {

    override fun getApplicableUastTypes(): List<Class<out UElement>> =
        listOf(UMethod::class.java)

    override fun createUastHandler(context: JavaContext): UElementHandler = object : UElementHandler() {
        override fun visitMethod(node: UMethod) {
            val contextReceiverEntryPointFqn =
                "com.alexvanyo.composelife.contextreceiverentrypoint.ContextReceiverEntryPoint"
            val contextReceiverEntryPointParameters = node.uastParameters
                .map { it.type }
                .filter { type ->
                    type.hasAnnotation(contextReceiverEntryPointFqn)
                }
                .flatMap { type ->
                    type.superTypes.toList() + type
                }
                .map { it as PsiClass }

            context.report(
                ISSUE,
                node,
                context.getNameLocation(node),
                "contextReceiverEntryPointParameters: ${node.getReceiver()}",
            )

            node.accept(
                object : AbstractUastVisitor() {
                    override fun visitSimpleNameReferenceExpression(node: USimpleNameReferenceExpression): Boolean {
                        context.report(
                            ISSUE,
                            node,
                            context.getNameLocation(node),
                            "expressionType: ${node.getExpressionType()}",
                        )
                        return false
                    }

//                    override fun visitExpression(node: UExpression): Boolean {
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "expressionType: ${node}",
//                        )
//                        return false
//                    }

//                    override fun visitSimpleNameReferenceExpression(node: USimpleNameReferenceExpression): Boolean {
//                        val element = node.resolveToUElement() ?: return false
//                        val containingUClass = element.getContainingUClass() ?: return false
//
//                        if (!containingUClass.hasAnnotation(contextReceiverEntryPointFqn)) return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "containingUClass: ${containingUClass.qualifiedName}",
//                        )
//
//                        if (containingUClass.javaPsi !in contextReceiverEntryPointParameters) {
//                            context.report(
//                                ISSUE,
//                                node,
//                                context.getNameLocation(node),
//                                "Call to ${node.resolvedName} on receiver type of ${containingUClass} is " +
//                                        "implicitly possible due to a super type, but should be made explicit.",
//                            )
//                        } else {
////                            context.report(
////                                ISSUE,
////                                node,
////                                context.getNameLocation(node),
////                                "TEST!",
////                            )
//                        }
//
//                        return false
//                    }

//                    override fun visitQualifiedReferenceExpression(node: UQualifiedReferenceExpression): Boolean {
//                        val declaration = node.getContainingDeclaration() ?: return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//                        return false
//                    }

//                    override fun visitMethod(node: UMethod): Boolean {
//                        val declaration = node.containingClass ?: return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//                        return false
//                    }

//                    override fun visitCallableReferenceExpression(node: UCallableReferenceExpression): Boolean {
//                        val declaration = node.resolveToUElement() ?: return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//                        return false
//                    }

//                    override fun visitField(node: UField): Boolean {
//                        val declaration = node.getContainingDeclaration() ?: return false
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//
//                        if (!declaration.hasAnnotation(contextReceiverEntryPointFqn)) return false
//
////                        context.report(
////                            ISSUE,
////                            node,
////                            context.getNameLocation(node),
////                            "declaration: $declaration",
////                        )
//
//                        if (declaration.javaPsi !in contextReceiverEntryPointParameters) {
//                            context.report(
//                                ISSUE,
//                                node,
//                                context.getNameLocation(node),
//                                "Call to $node on receiver type of $declaration is " +
//                                        "implicitly possible due to a super type, but should be made explicit.",
//                            )
//                        }
//
//                        return false
//                    }

//                    override fun visitExpression(node: UExpression): Boolean {
//                        val declaration = node.getContainingDeclaration() ?: return false
//                        if (!declaration.hasAnnotation(contextReceiverEntryPointFqn)) return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//
//                        if (declaration.javaPsi !in contextReceiverEntryPointParameters) {
//                            context.report(
//                                ISSUE,
//                                node,
//                                context.getNameLocation(node),
//                                "Call to $node on receiver type of $declaration is " +
//                                        "implicitly possible due to a super type, but should be made explicit.",
//                            )
//                        }
//
//                        return false
//                    }

//                    override fun visitCallExpression(node: UCallExpression): Boolean {
//                        val declaration = node.resolveToUElement() ?: return false
//
//                        context.report(
//                            ISSUE,
//                            node,
//                            context.getNameLocation(node),
//                            "declaration: $declaration",
//                        )
//                        val containingUClass = declaration.getContainingUClass() ?: return false
//
//                        if (!containingUClass.hasAnnotation(contextReceiverEntryPointFqn)) return false
//
//                        if (containingUClass.javaPsi !in contextReceiverEntryPointParameters) {
//                            context.report(
//                                ISSUE,
//                                node,
//                                context.getNameLocation(node),
//                                "Call to ${node.methodName} on receiver type of ${node.receiver} is " +
//                                        "implicitly possible due to a super type, but should be made explicit.",
//                            )
//                        } else {
//                            context.report(
//                                ISSUE,
//                                node,
//                                context.getNameLocation(node),
//                                "TEST!",
//                            )
//                        }
//
//                        return false
//                    }
                }
            )
        }
    }

    companion object {
        @JvmField
        val ISSUE: Issue = Issue.create(
            id = "ContextReceiverEntryPoint",
            briefDescription = "Invalid use of transitive entry point dependencies",
            explanation = "A member available in the scope of this entry point ",
            category = Category.CUSTOM_LINT_CHECKS,
            priority = 10,
            severity = Severity.ERROR,
            implementation = Implementation(
                ContextReceiverEntryPointDetector::class.java,
                Scope.JAVA_FILE_SCOPE,
            ),
        )
    }
}
