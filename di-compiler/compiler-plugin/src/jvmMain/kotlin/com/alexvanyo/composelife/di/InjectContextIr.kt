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

@file:Suppress("ReturnCount")

package com.alexvanyo.composelife.di

import org.jetbrains.kotlin.backend.common.extensions.IrGenerationExtension
import org.jetbrains.kotlin.backend.common.extensions.IrPluginContext
import org.jetbrains.kotlin.backend.common.lower.DeclarationIrBuilder
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.builders.irBlockBody
import org.jetbrains.kotlin.ir.builders.irCall
import org.jetbrains.kotlin.ir.builders.irGet
import org.jetbrains.kotlin.ir.builders.irReturn
import org.jetbrains.kotlin.ir.declarations.IrDeclarationOrigin
import org.jetbrains.kotlin.ir.declarations.IrModuleFragment
import org.jetbrains.kotlin.ir.declarations.IrParameterKind
import org.jetbrains.kotlin.ir.declarations.IrSimpleFunction
import org.jetbrains.kotlin.ir.symbols.UnsafeDuringIrConstructionAPI
import org.jetbrains.kotlin.ir.types.classOrNull
import org.jetbrains.kotlin.ir.util.functions
import org.jetbrains.kotlin.ir.visitors.IrElementTransformerVoid
import org.jetbrains.kotlin.ir.visitors.transformChildrenVoid

class InjectContextIr : IrGenerationExtension {
    override fun generate(moduleFragment: IrModuleFragment, pluginContext: IrPluginContext) {
        moduleFragment.transformChildrenVoid(
            InjectContextIrTransformer(pluginContext),
        )
    }
}

@OptIn(UnsafeDuringIrConstructionAPI::class)
private class InjectContextIrTransformer(private val pluginContext: IrPluginContext) : IrElementTransformerVoid() {

    override fun visitSimpleFunction(declaration: IrSimpleFunction): IrStatement {
        val origin = declaration.origin
        val isFromOurPlugin = origin is IrDeclarationOrigin.GeneratedByPlugin &&
            origin.pluginKey == InjectContextFirExtension.Key
        if (!isFromOurPlugin) {
            return super.visitSimpleFunction(declaration)
        }

        if (declaration.body != null) return super.visitSimpleFunction(declaration)

        val ctxParam = declaration.parameters.firstOrNull { it.kind == IrParameterKind.Context }
            ?: return super.visitSimpleFunction(declaration)

        val contextClassSymbol = ctxParam.type.classOrNull
            ?: return super.visitSimpleFunction(declaration)

        val regularParams = declaration.parameters.filter { it.kind == IrParameterKind.Regular }
        val invokeFunction = contextClassSymbol.owner.functions
            .firstOrNull { it.name.asString() == "invoke" }
            ?: return super.visitSimpleFunction(declaration)

        val builder = DeclarationIrBuilder(pluginContext, declaration.symbol)

        val invokeCall = builder.irCall(invokeFunction).apply {
            val dispatchReceiverParam = invokeFunction.parameters.firstOrNull {
                it.kind == IrParameterKind.DispatchReceiver
            }
            if (dispatchReceiverParam == null) {
                val paramKinds = invokeFunction.parameters.map { "${it.name}: ${it.kind}" }
                error(
                    "target invoke function '${invokeFunction.name}' has no dispatch receiver. " +
                        "Parameters: $paramKinds",
                )
            }
            arguments[invokeFunction.parameters.indexOf(dispatchReceiverParam)] = builder.irGet(ctxParam)

            val invokeRegularParams = invokeFunction.parameters.filter { it.kind == IrParameterKind.Regular }
            invokeRegularParams.forEach { param ->
                val sourceParam = regularParams.firstOrNull { it.name == param.name }
                if (sourceParam != null) {
                    arguments[invokeFunction.parameters.indexOf(param)] = builder.irGet(sourceParam)
                }
            }
        }

        declaration.body = builder.irBlockBody {
            +irReturn(invokeCall)
        }

        return super.visitSimpleFunction(declaration)
    }
}
