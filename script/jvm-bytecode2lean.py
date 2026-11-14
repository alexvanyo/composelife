#!/usr/bin/env python3
#
# Copyright 2026 The Android Open Source Project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
"""Generic JVM `.class` bytecode-to-Lean 4 lifter.

Disassembles compiled JVM `.class` files with `javap -c -p` and translates each
method's bytecode instructions into pure Lean 4 `List JvmInstr` definitions.
All operational semantics, equivalence theorems, and proofs live in `.lean`
source files rather than in this script.

Usage:

    ./script/jvm-bytecode2lean.py \\
        --class-file path/to/FooKt.class \\
        --import Module.JvmSemantics \\
        --namespace Module.JvmBytecode \\
        -o build/generated/lean/jvm/Module/JvmBytecode.lean
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys


SIMPLE_OPCODES = frozenset({
    "nop", "dup", "pop", "swap", "athrow",
    "iadd", "isub", "imul", "ineg", "iand", "ior", "ixor", "ishl", "ishr", "iushr",
    "ladd", "lsub", "lmul", "land", "lor", "lxor", "lshl", "lshr", "lushr",
    "dneg", "dcmpg", "dcmpl",
    "i2l", "l2i", "i2b", "lcmp",
    "ireturn", "lreturn", "areturn", "dreturn",
})

BRANCH_OPCODES = frozenset({
    "ifeq", "ifne", "iflt", "ifle", "ifgt", "ifge",
    "ifnull", "ifnonnull",
    "if_icmpeq", "if_icmpne", "if_icmplt", "goto",
})


@dataclass(frozen=True)
class DisassembledMethod:
    """A single JVM method disassembled by `javap -c -p`."""

    owner_internal: str
    jvm_name: str
    descriptor_params: str
    raw_instrs: list[tuple[int, str, str]]


def to_u32_lit(val: int | str) -> str:
    """Formats a signed 32-bit integer as an unsigned 32-bit Lean literal."""
    v = int(val)
    return str((1 << 32) + v if v < 0 else v)


def to_u64_lit(val_str: str) -> str:
    """Formats a signed 64-bit `javap` long literal as an unsigned 64-bit Lean literal."""
    v = int(val_str.rstrip("lL"))
    return str((1 << 64) + v if v < 0 else v)


def lean_str_lit(s: str) -> str:
    """Escapes a Python string as a Lean 4 string literal."""
    escaped = (
        s.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )
    return f'"{escaped}"'


def parse_method_ref(comment: str, default_owner: str) -> tuple[str, str, str]:
    """Extracts `(owner, method_name, descriptor)` from a `javap` invoke comment."""
    m = re.search(r"//\s*(?:Interface)?Method\s+(.*)", comment)
    if not m:
        raise ValueError(f"Expected Method/InterfaceMethod comment, got: {comment!r}")
    ref = m.group(1).strip()
    target, sep, desc = ref.partition(":")
    if not sep:
        raise ValueError(f"Missing descriptor in method ref: {ref!r}")
    if "." in target:
        owner, _, member = target.partition(".")
    else:
        owner, member = default_owner, target
    return owner, member.strip('"'), desc


def parse_field_ref(comment: str, default_owner: str) -> tuple[str, str, str]:
    """Extracts `(owner, field_name, descriptor)` from a `javap` Field comment."""
    m = re.search(r"//\s*Field\s+(.*)", comment)
    if not m:
        raise ValueError(f"Expected Field comment, got: {comment!r}")
    ref = m.group(1).strip()
    target, sep, desc = ref.partition(":")
    if not sep:
        raise ValueError(f"Missing descriptor in field ref: {ref!r}")
    if "." in target:
        owner, _, member = target.partition(".")
    else:
        owner, member = default_owner, target
    return owner, member.strip('"'), desc


def parse_class_ref(comment: str) -> str:
    """Extracts the internal class name from a `javap` class comment."""
    m = re.search(r"//\s*class\s+(\S+)", comment)
    if not m:
        raise ValueError(f"Expected class comment, got: {comment!r}")
    return m.group(1).strip('"')


def disassemble_class_file(class_file: Path) -> list[DisassembledMethod]:
    """Disassembles one `.class` file with `javap -c -p`."""
    output = subprocess.check_output(["javap", "-c", "-p", str(class_file)], text=True)
    class_re = re.compile(r"class\s+([A-Za-z0-9_.$-]+)")
    sig_re = re.compile(
        r"^\s{2}(?:.*\s)([A-Za-z0-9_$-]+)\(([^)]*)\);$"
    )
    instr_re = re.compile(r"^\s+(\d+):\s+(\S+)(?:\s+(.*))?$")

    owner_internal = class_file.stem
    results: list[DisassembledMethod] = []
    cur_name: str | None = None
    cur_params = ""
    cur_instrs: list[tuple[int, str, str]] = []
    in_code = False

    def flush_current() -> None:
        if cur_name is not None and cur_instrs:
            results.append(
                DisassembledMethod(
                    owner_internal=owner_internal,
                    jvm_name=cur_name,
                    descriptor_params=cur_params,
                    raw_instrs=cur_instrs,
                )
            )

    for line in output.splitlines():
        if cur_name is None and not in_code:
            cm = class_re.search(line)
            if cm and line.rstrip().endswith("{"):
                owner_internal = cm.group(1).replace(".", "/")
        sig_match = sig_re.match(line)
        if sig_match:
            flush_current()
            cur_name = sig_match.group(1)
            cur_params = sig_match.group(2)
            cur_instrs = []
            in_code = False
            continue
        if cur_name is None:
            continue
        stripped = line.strip()
        if stripped == "Code:":
            in_code = True
            continue
        if stripped == "" or stripped.endswith(":") or stripped == "}":
            in_code = False
            continue
        if in_code:
            im = instr_re.match(line)
            if im:
                cur_instrs.append((int(im.group(1)), im.group(2), (im.group(3) or "").strip()))

    flush_current()
    return results


def lift_method(method: DisassembledMethod) -> list[str]:
    """Translates raw `(offset, opcode, arg)` tuples into generic Lean `JvmInstr` strings."""
    offset_to_idx = {off: idx for idx, (off, _, _) in enumerate(method.raw_instrs)}
    lifted: list[str] = []

    for _, op, arg in method.raw_instrs:
        if op in SIMPLE_OPCODES:
            lifted.append(f".{op}")
        elif op == "return":
            lifted.append(".vreturn")
        elif op == "aconst_null":
            lifted.append(".aconstNull")
        elif op == "dconst_0":
            lifted.append(".dconst0")
        elif op == "dconst_1":
            lifted.append(".dconst1")
        elif op.startswith("iconst_"):
            suffix = op.removeprefix("iconst_")
            val = -1 if suffix == "m1" else int(suffix)
            lifted.append(f".iconst {to_u32_lit(val)}")
        elif op in ("bipush", "sipush"):
            lifted.append(f".iconst {to_u32_lit(arg)}")
        elif op in ("ldc", "ldc_w"):
            int_m = re.search(r"// int (-?\d+)", arg)
            str_m = re.search(r"// String (.*)", arg)
            if int_m:
                lifted.append(f".iconst {to_u32_lit(int_m.group(1))}")
            elif str_m:
                lifted.append(f".ldcStr {lean_str_lit(str_m.group(1))}")
            else:
                raise ValueError(f"Unsupported constant pool entry for {op}: {arg}")
        elif op.startswith("lconst_"):
            lifted.append(f".lconst {op.removeprefix('lconst_')}")
        elif op == "ldc2_w":
            m = re.search(r"// long (-?\d+l?)", arg)
            if not m:
                raise ValueError(f"Unsupported constant pool entry for {op}: {arg}")
            lifted.append(f".lconst {to_u64_lit(m.group(1))}")
        elif op.startswith(("iload", "lload", "aload", "dload", "istore", "lstore", "astore", "dstore")):
            base, _, slot_suffix = op.partition("_")
            slot = int(slot_suffix) if slot_suffix else int(arg)
            lifted.append(f".{base} {slot}")
        elif op in BRANCH_OPCODES:
            target_idx = offset_to_idx[int(arg)]
            lifted.append(f".{op} {target_idx}")
        elif op == "new":
            cls = parse_class_ref(arg)
            lifted.append(f".newClass {lean_str_lit(cls)}")
        elif op in ("checkcast", "instanceof"):
            cls = parse_class_ref(arg)
            lifted.append(f".{op} {lean_str_lit(cls)}")
        elif op == "getfield":
            owner, member, desc = parse_field_ref(arg, method.owner_internal)
            lifted.append(f".getfield {lean_str_lit(owner)} {lean_str_lit(member)} {lean_str_lit(desc)}")
        elif op in ("invokestatic", "invokevirtual", "invokespecial", "invokeinterface"):
            owner, member, desc = parse_method_ref(arg, method.owner_internal)
            lifted.append(f".{op} {lean_str_lit(owner)} {lean_str_lit(member)} {lean_str_lit(desc)}")
        else:
            raise ValueError(f"Unsupported JVM opcode: {op} {arg}")

    return lifted


def strip_kotlin_mangle(jvm_name: str) -> str:
    """Strips Kotlin inline-class hash suffix `-xxxxxxx` from a method name."""
    return re.sub(r"--?[A-Za-z0-9_-]{7}$", "", jvm_name)


def assign_lean_names(methods: list[DisassembledMethod]) -> list[tuple[DisassembledMethod, str]]:
    """Assigns clean, unique Lean identifier names `<name>_prog` for each method."""
    used: dict[str, int] = {}
    assigned: list[tuple[DisassembledMethod, str]] = []
    for m in methods:
        base = strip_kotlin_mangle(m.jvm_name)
        clean = re.sub(r"[^A-Za-z0-9_]", "_", base)
        count = used.get(clean, 0)
        used[clean] = count + 1
        final_name = f"{clean}_prog" if count == 0 else f"{clean}_{count}_prog"
        assigned.append((m, final_name))
    return assigned


def generate_lean_bytecode_file(
    class_files: list[Path],
    imports: list[str],
    namespace: str,
    instr_type: str,
    required_methods: list[str],
) -> tuple[str, int, int]:
    """Lifts bytecode from `class_files` into pure Lean data definitions."""
    all_methods: list[DisassembledMethod] = []
    for cf in class_files:
        all_methods.extend(disassemble_class_file(cf))

    lifted_entries: list[tuple[DisassembledMethod, list[str]]] = []
    skipped: list[tuple[str, str]] = []
    required_set = set(required_methods)

    for m in all_methods:
        matches_required = m.jvm_name in required_set or strip_kotlin_mangle(m.jvm_name) in required_set
        try:
            instrs = lift_method(m)
        except ValueError as exc:
            if matches_required:
                raise ValueError(f"Required method {m.jvm_name} failed to lift: {exc}") from exc
            skipped.append((m.jvm_name, str(exc)))
            continue
        lifted_entries.append((m, instrs))

    assigned = assign_lean_names([m for m, _ in lifted_entries])
    lifted_by_obj = {id(m): instrs for m, instrs in lifted_entries}

    found_names = {m.jvm_name for m, _ in assigned} | {strip_kotlin_mangle(m.jvm_name) for m, _ in assigned} | {
        lean_name for _, lean_name in assigned
    }
    missing = [req for req in required_methods if req not in found_names]
    if missing:
        raise KeyError(f"Required methods not found or failed to lift: {missing}")

    lines: list[str] = [
        "/-",
        " * Automatically lifted JVM bytecode definitions (generated by script/jvm-bytecode2lean.py).",
        " -/",
        "",
    ]
    for imp in imports:
        lines.append(f"import {imp}")
    if imports:
        lines.append("")
    if namespace:
        lines.append(f"namespace {namespace}")
        lines.append("")

    total_instrs = 0
    for m, lean_name in assigned:
        instrs = lifted_by_obj[id(m)]
        total_instrs += len(instrs)
        lines.append(f"def {lean_name} : List {instr_type} := [{', '.join(instrs)}]")

    if skipped:
        lines.append("")
        lines.append(f"/- Skipped {len(skipped)} methods using out-of-subset JVM opcodes. -/")

    if namespace:
        lines.append("")
        lines.append(f"end {namespace}")
    lines.append("")

    return "\n".join(lines), len(assigned), total_instrs


def main(argv: list[str] | None = None) -> int:
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Lift compiled JVM .class bytecode into pure Lean 4 `List JvmInstr` definitions.",
    )
    parser.add_argument(
        "--class-file",
        type=Path,
        action="append",
        default=[],
        help="Compiled `.class` file to disassemble and lift (repeatable).",
    )
    parser.add_argument(
        "--class-dir",
        type=Path,
        action="append",
        default=[],
        help="Directory to search recursively for `.class` files (repeatable).",
    )
    parser.add_argument(
        "--import",
        dest="imports",
        action="append",
        default=[],
        help="Lean module to import at the top of the generated file (repeatable).",
    )
    parser.add_argument(
        "--namespace",
        default="",
        help="Optional Lean namespace wrapping the lifted definitions.",
    )
    parser.add_argument(
        "--instr-type",
        default="JvmInstr",
        help="Lean instruction type name (default: JvmInstr).",
    )
    parser.add_argument(
        "--require",
        action="append",
        default=[],
        help="Require that this JVM/Lean method name was successfully lifted (repeatable).",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=None,
        help="Write the generated Lean 4 file to this path (defaults to stdout).",
    )
    args = parser.parse_args(argv)

    class_files: list[Path] = []
    for cf in args.class_file:
        if not cf.is_file():
            raise FileNotFoundError(f"Class file not found: {cf}")
        class_files.append(cf)
    for cd in args.class_dir:
        if not cd.is_dir():
            raise FileNotFoundError(f"Class directory not found: {cd}")
        class_files.extend(sorted(cd.rglob("*.class")))

    if not class_files:
        raise ValueError("Provide at least one --class-file or --class-dir.")

    lean_source, method_count, total_instrs = generate_lean_bytecode_file(
        class_files=class_files,
        imports=args.imports,
        namespace=args.namespace,
        instr_type=args.instr_type,
        required_methods=args.require,
    )

    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(lean_source, encoding="utf-8")
        print(f"Lifted {method_count} methods ({total_instrs} JVM instructions) to {args.output}.")
    else:
        sys.stdout.write(lean_source)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
