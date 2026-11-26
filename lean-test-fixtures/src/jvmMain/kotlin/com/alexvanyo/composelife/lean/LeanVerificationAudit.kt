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

package com.alexvanyo.composelife.lean

import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

private val allowedAxioms = setOf("propext", "Classical.choice", "Quot.sound")

private val forbiddenLeanBodyRules = listOf(
    "bv_decide" to Regex("""\bbv_decide\b"""),
    "axiom" to Regex("""\baxiom\b"""),
    "unsafe" to Regex("""\bunsafe\b"""),
    "partial" to Regex("""\bpartial\b"""),
    // Anything that runs metaprograms could add declarations (such as forged axioms) or bypass the kernel.
    "run_meta" to Regex("""\brun_meta\b"""),
    "run_elab" to Regex("""\brun_elab\b"""),
    "run_cmd" to Regex("""\brun_cmd\b"""),
    "run_tac" to Regex("""\brun_tac\b"""),
    "by_elab" to Regex("""\bby_elab\b"""),
    "#eval" to Regex("""(?<![A-Za-z0-9_])#eval\b"""),
    "#exit" to Regex("""(?<![A-Za-z0-9_])#exit\b"""),
    "elab" to Regex("""\belab(?:_rules)?\b"""),
    "macro" to Regex("""\bmacro(?:_rules)?\b"""),
    "syntax" to Regex("""\b(?:syntax|declare_syntax_cat)\b"""),
    "initialize" to Regex("""\binitialize\b"""),
    "debug/trust option" to Regex("""\bset_option\s+(?:debug|trust)"""),
    "sorry" to Regex("""\bsorry\b"""),
    "admit" to Regex("""\badmit\b"""),
    "implemented_by/extern/csimp attribute" to
        Regex("""(?:@\[|\battribute\s*\[)[^\]"]*\b(?:implemented_by|extern|csimp)\b"""),
)

internal fun validateLeanBody(theoremName: String, leanBody: String) {
    val codeOnly = stripLeanCommentsAndStrings(leanBody)
    val matched = forbiddenLeanBodyRules.firstNotNullOfOrNull { (label, regex) ->
        if (regex.containsMatchIn(codeOnly)) label else null
    }
    assertTrue(
        matched == null,
        "Theorem $theoremName body contains forbidden Lean construct `$matched`.",
    )
}

internal fun buildKernelAxiomAuditSnippet(spec: JvmBytecodeVerificationSpec, theoremName: String): String = """
    |run_meta do
    |  let env ← Lean.getEnv
    |  let thmName : Lean.Name := ``$theoremName
    |  let some ci := env.find? thmName |
    |    throwError "Expected proven theorem {thmName} in environment."
    |  unless ci matches .thmInfo _ do
    |    throwError "Declaration {thmName} must be a theorem, not an axiom or definition."
    |  unless Jvm.isNonTrivialTheoremType ci.type do
    |    throwError "Theorem {thmName} must have a non-trivial statement."
    |  let ns : Lean.Name := `${spec.realBytecodeNamespace}
    |  let realProgs := ci.type.getUsedConstants.filter (fun c => ns.isPrefixOf c)
    |  unless realProgs.any (Jvm.provesExecutionOf ci.type) do
    |    throwError "Theorem {thmName} must conclude about running (`runJvm*`) lifted real bytecode under {ns}."
    |  for h in Jvm.theoremBinderTypes ci.type do
    |    if realProgs.any (Jvm.executesProg h) then
    |      throwError "Theorem {thmName} must not assume running real bytecode in a hypothesis."
    |  let bad ← Jvm.nonStandardAxioms thmName
    |  unless bad.isEmpty do
    |    throwError "Theorem depended on non-standard axioms: {bad.toList}"
""".trimMargin()

internal fun assertAxiomsAreStandard(theoremName: String, leanOutput: String) {
    assertFalse(
        leanOutput.contains("sorryAx"),
        "Theorem $theoremName relied on sorryAx!\n$leanOutput",
    )
    val noAxiomsMarker = "'$theoremName' does not depend on any axioms"
    if (leanOutput.contains(noAxiomsMarker)) {
        return
    }
    val dependsPrefix = "'$theoremName' depends on axioms: ["
    val startIndex = leanOutput.indexOf(dependsPrefix)
    assertTrue(
        startIndex >= 0,
        "Expected `#print axioms $theoremName` output in Lean stdout.\n$leanOutput",
    )
    val listStart = startIndex + dependsPrefix.length
    val listEnd = leanOutput.indexOf(']', startIndex = listStart)
    assertTrue(listEnd > listStart, "Malformed axioms output for $theoremName.\n$leanOutput")
    val axioms = leanOutput.substring(listStart, listEnd)
        .split(',')
        .map { it.trim() }
        .filter { it.isNotEmpty() }
    // `bv_check` axioms are only name-checked here; the kernel audit snippet re-runs each one's certificate.
    val unexpected = axioms.filterNot { axiom ->
        axiom in allowedAxioms || "._native.bv_decide." in axiom
    }
    assertEquals(
        emptyList(),
        unexpected,
        "Theorem $theoremName depends on non-standard axioms: $unexpected\n$leanOutput",
    )
}

private fun stripLeanCommentsAndStrings(source: String): String {
    val out = StringBuilder(source.length)
    var i = 0
    while (i < source.length) {
        i = when {
            source.startsWith("--", i) -> skipLineComment(source, i, out)

            source.startsWith("/-", i) -> skipBlockComment(source, i, out)

            source.startsWith("'\\\"'", i) || source.startsWith("'\"'", i) -> {
                val len = if (source[i + 1] == '\\') 4 else 3
                repeat(len) { out.append(' ') }
                i + len
            }

            source[i] == '"' -> skipDoubleQuotedString(source, i, out)

            else -> {
                out.append(source[i])
                i + 1
            }
        }
    }
    return out.toString()
}

private fun skipLineComment(source: String, start: Int, out: StringBuilder): Int {
    var i = start
    while (i < source.length && source[i] != '\n') {
        out.append(' ')
        i++
    }
    return i
}

private fun skipBlockComment(source: String, start: Int, out: StringBuilder): Int {
    var i = start + 2
    var depth = 1
    out.append("  ")
    while (i < source.length && depth > 0) {
        when {
            source.startsWith("/-", i) -> {
                depth++
                out.append("  ")
                i += 2
            }

            source.startsWith("-/", i) -> {
                depth--
                out.append("  ")
                i += 2
            }

            else -> {
                out.append(if (source[i] == '\n') '\n' else ' ')
                i++
            }
        }
    }
    return i
}

private fun skipDoubleQuotedString(source: String, start: Int, out: StringBuilder): Int {
    out.append(' ')
    var i = start + 1
    while (i < source.length) {
        val ch = source[i]
        if (ch == '\\' && i + 1 < source.length) {
            out.append(' ')
            out.append(if (source[i + 1] == '\n') '\n' else ' ')
            i += 2
        } else {
            out.append(if (ch == '\n' && ch != '"') '\n' else ' ')
            i++
            if (ch == '"') {
                break
            }
        }
    }
    return i
}
