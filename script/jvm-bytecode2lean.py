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

Disassembles compiled JVM `.class` files with `javap -v -p` and translates each
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
import struct
import subprocess
import sys


SIMPLE_OPCODES = frozenset({
    "nop", "dup", "pop", "swap", "athrow",
    "iadd", "isub", "imul", "idiv", "irem", "ineg", "iand", "ior", "ixor", "ishl", "ishr", "iushr",
    "ladd", "lsub", "lmul", "ldiv", "lrem", "land", "lor", "lxor", "lshl", "lshr", "lushr",
    "fadd", "fsub", "fmul", "fdiv", "fneg", "fcmpg", "fcmpl",
    "dadd", "dsub", "dmul", "ddiv", "dneg", "dcmpg", "dcmpl",
    "i2l", "l2i", "i2b", "i2c", "i2s", "i2f", "l2f", "f2i", "f2l", "i2d", "l2d", "d2i", "d2l", "f2d", "d2f", "lcmp",
    "arraylength",
    "aaload", "aastore",
    "baload", "bastore",
    "caload", "castore",
    "saload", "sastore",
    "iaload", "iastore",
    "laload", "lastore",
    "faload", "fastore",
    "daload", "dastore",
    "ireturn", "lreturn", "areturn", "freturn", "dreturn",
})

BRANCH_OPCODES = frozenset({
    "ifeq", "ifne", "iflt", "ifle", "ifgt", "ifge",
    "ifnull", "ifnonnull",
    "if_icmpeq", "if_icmpne", "if_icmplt", "if_icmpge", "if_icmpgt", "if_icmple",
    "if_acmpeq", "if_acmpne",
    "goto",
})

_CODE_SECTION_END_PREFIXES = (
    "Exception table:",
    "LineNumberTable:",
    "LocalVariableTable:",
    "LocalVariableTypeTable:",
    "StackMapTable:",
    "RuntimeVisibleTypeAnnotations:",
    "RuntimeInvisibleTypeAnnotations:",
)


@dataclass(frozen=True)
class DisassembledMethod:
    """A single JVM method disassembled by `javap -v -p`."""

    owner_internal: str
    jvm_name: str
    descriptor_params: str
    raw_instrs: list[tuple[int, str, str]]
    const_pool: dict[int, tuple[str, str]]
    bootstrap_methods: dict[int, tuple[str, str]]
    has_exception_table: bool = False


def to_u32_lit(val: int | str) -> str:
    """Formats a signed 32-bit integer as an unsigned 32-bit Lean literal."""
    v = int(val)
    return str((1 << 32) + v if v < 0 else v)


def to_i32_lit(val: int | str) -> str:
    """Formats a signed 32-bit integer as a Lean `Int32` literal."""
    v = int(val)
    return f"({v})" if v < 0 else str(v)


def to_u64_lit(val_str: str) -> str:
    """Formats a signed 64-bit `javap` long literal as an unsigned 64-bit Lean literal."""
    v = int(val_str.rstrip("lL"))
    return str((1 << 64) + v if v < 0 else v)


def lean_str_lit(s: str) -> str:
    """Escapes a Python string as a Lean 4 string literal."""
    out: list[str] = ['"']
    for ch in s:
        code = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif code < 0x20 or code == 0x7F:
            out.append(f"\\x{code:02x}")
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def read_class_const_pool(class_file: Path) -> tuple[dict[int, str], dict[int, int], dict[int, int]]:
    """Reads exact `CONSTANT_Utf8`, `CONSTANT_Float`, and `CONSTANT_Double` entries from a `.class` file."""
    data = class_file.read_bytes()
    if len(data) < 10 or struct.unpack_from(">I", data, 0)[0] != 0xCAFEBABE:
        raise ValueError(f"Not a valid JVM class file: {class_file}")
    cp_count = struct.unpack_from(">H", data, 8)[0]
    pos = 10
    utf8_pool: dict[int, str] = {}
    float_bits_pool: dict[int, int] = {}
    double_bits_pool: dict[int, int] = {}
    idx = 1
    while idx < cp_count:
        tag = data[pos]
        pos += 1
        if tag == 1:  # CONSTANT_Utf8
            length = struct.unpack_from(">H", data, pos)[0]
            pos += 2
            raw = data[pos:pos + length]
            pos += length
            s = raw.replace(b"\xc0\x80", b"\x00").decode("utf-8", errors="surrogatepass")
            try:
                s = s.encode("utf-16", errors="surrogatepass").decode("utf-16")
            except UnicodeDecodeError:
                pass
            utf8_pool[idx] = s
            idx += 1
        elif tag == 3:  # Integer
            pos += 4
            idx += 1
        elif tag == 4:  # Float (exact IEEE 754 binary32 bits)
            float_bits_pool[idx] = struct.unpack_from(">I", data, pos)[0]
            pos += 4
            idx += 1
        elif tag == 5:  # Long
            pos += 8
            idx += 2
        elif tag == 6:  # Double (exact IEEE 754 binary64 bits)
            double_bits_pool[idx] = struct.unpack_from(">Q", data, pos)[0]
            pos += 8
            idx += 2
        elif tag in (7, 8, 16, 19, 20):  # Class, String, MethodType, Module, Package
            pos += 2
            idx += 1
        elif tag in (9, 10, 11, 12, 17, 18):  # Fieldref..InvokeDynamic
            pos += 4
            idx += 1
        elif tag == 15:  # MethodHandle
            pos += 3
            idx += 1
        else:
            raise ValueError(f"Unsupported constant pool tag {tag} in {class_file} at {pos - 1}")
    return utf8_pool, float_bits_pool, double_bits_pool


def unescape_javap_utf8(raw: str) -> str:
    """Decodes `javap -v` constant-pool Utf8 escape sequences into a Python string."""
    out: list[str] = []
    i = 0
    n = len(raw)
    while i < n:
        ch = raw[i]
        if ch == "\\" and i + 1 < n:
            nxt = raw[i + 1]
            if nxt == "u" and i + 5 < n:
                hex_part = raw[i + 2:i + 6]
                try:
                    out.append(chr(int(hex_part, 16)))
                    i += 6
                    continue
                except ValueError:
                    pass
            escapes = {"n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f", "\\": "\\", '"': '"', "'": "'"}
            if nxt in escapes:
                out.append(escapes[nxt])
                i += 2
                continue
        out.append(ch)
        i += 1
    return "".join(out)


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
    return owner.strip('"'), member.strip('"'), desc


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
    return owner.strip('"'), member.strip('"'), desc


def parse_class_ref(comment: str) -> str:
    """Extracts the internal class name from a `javap` class comment."""
    m = re.search(r"//\s*class\s+(\S+)", comment)
    if not m:
        raise ValueError(f"Expected class comment, got: {comment!r}")
    return m.group(1).strip('"')


def parse_invokedynamic_ref(comment: str) -> tuple[int, str, str]:
    """Extracts `(bsm_index, method_name, descriptor)` from a `javap` InvokeDynamic comment."""
    m = re.search(r"//\s*InvokeDynamic\s+#(\d+):([^:]+):(\S+)", comment)
    if not m:
        raise ValueError(f"Expected InvokeDynamic comment, got: {comment!r}")
    return int(m.group(1)), m.group(2).strip('"'), m.group(3)


def disassemble_class_file(class_file: Path) -> list[DisassembledMethod]:
    """Disassembles one `.class` file with `javap -v -p`."""
    output = subprocess.check_output(["javap", "-v", "-p", str(class_file)], text=True)
    class_re = re.compile(r"(?:class|interface|enum)\s+([A-Za-z0-9_.$-]+)")
    cp_re = re.compile(r"^\s+#(\d+)\s+=\s+(\S+)(.*)$")
    sig_re = re.compile(r"^\s{2}(?:.*\s)?([A-Za-z0-9_.$-]+)\(([^)]*)\)(?:\s+throws\s+[^;]+)?;")
    clinit_re = re.compile(r"^\s{2}static\s*\{\};$")
    instr_re = re.compile(r"^\s+(\d+):\s+([a-z][a-z0-9_]*)(?:\s+(.*))?$")
    bsm_entry_re = re.compile(r"^\s{2}(\d+):\s+#\d+\s+(.*)$")
    bsm_arg_re = re.compile(r"^\s+#(\d+)\s*(.*)$")

    owner_internal = class_file.stem
    utf8_pool: dict[int, str] = {}
    const_pool_raw: dict[int, tuple[str, str]] = {}
    bootstrap_methods_raw: dict[int, tuple[str, int | None, str]] = {}

    lines = output.splitlines()
    in_cp = False
    in_bsm = False
    cur_bsm_idx: int | None = None
    in_bsm_args = False
    bsm_arg_pos = 0

    # First pass: collect constant pool and BootstrapMethods section.
    for line in lines:
        stripped = line.strip()
        if stripped == "Constant pool:":
            in_cp = True
            in_bsm = False
            continue
        if stripped == "BootstrapMethods:":
            in_bsm = True
            in_cp = False
            cur_bsm_idx = None
            in_bsm_args = False
            continue
        if stripped == "{":
            in_cp = False
            continue
        if in_cp:
            cm = cp_re.match(line)
            if cm:
                idx = int(cm.group(1))
                tag = cm.group(2)
                rest = cm.group(3)
                if tag == "Utf8":
                    # `javap -v` pads `= Utf8` with 15 spaces for non-empty values and 0 spaces for "".
                    val_raw = rest[15:] if len(rest) >= 15 else ""
                    utf8_pool[idx] = unescape_javap_utf8(val_raw)
                else:
                    const_pool_raw[idx] = (tag, rest.strip())
            elif stripped == "" or not line.startswith("  "):
                in_cp = False
        elif in_bsm:
            if not line.startswith("  ") and stripped != "":
                in_bsm = False
                continue
            bm = bsm_entry_re.match(line)
            if bm:
                cur_bsm_idx = int(bm.group(1))
                desc_part = bm.group(2)
                in_bsm_args = False
                bsm_arg_pos = 0
                if "makeConcatWithConstants" in desc_part:
                    kind = "makeConcatWithConstants"
                elif "java/lang/invoke/LambdaMetafactory" in desc_part:
                    kind = "LambdaMetafactory"
                else:
                    kind = desc_part
                bootstrap_methods_raw[cur_bsm_idx] = (kind, None, "")
                continue
            if stripped == "Method arguments:":
                in_bsm_args = True
                bsm_arg_pos = 0
                continue
            if in_bsm_args and cur_bsm_idx is not None:
                am = bsm_arg_re.match(line)
                if am:
                    kind, existing_cp, existing_txt = bootstrap_methods_raw[cur_bsm_idx]
                    want_pos = 1 if kind == "LambdaMetafactory" else 0
                    if bsm_arg_pos == want_pos and existing_cp is None:
                        bootstrap_methods_raw[cur_bsm_idx] = (
                            kind,
                            int(am.group(1)),
                            unescape_javap_utf8(am.group(2)),
                        )
                        in_bsm_args = False
                    bsm_arg_pos += 1

    # Overlay exact `CONSTANT_Utf8`, `CONSTANT_Float`, and `CONSTANT_Double` bits from binary `.class` bytes.
    utf8_exact, float_bits_exact, double_bits_exact = read_class_const_pool(class_file)
    utf8_pool.update(utf8_exact)

    const_pool: dict[int, tuple[str, str]] = {}
    for idx, val in utf8_pool.items():
        const_pool[idx] = ("Utf8", val)
    for idx, (tag, rest) in const_pool_raw.items():
        if tag == "String":
            m_ref = re.match(r"#(\d+)", rest)
            if m_ref:
                const_pool[idx] = ("String", utf8_pool.get(int(m_ref.group(1)), ""))
        elif tag == "Integer":
            const_pool[idx] = ("Integer", rest.split()[0])
        elif tag == "Long":
            const_pool[idx] = ("Long", rest.split()[0])
        elif tag == "Float":
            bits = float_bits_exact.get(idx)
            const_pool[idx] = ("Float", str(bits) if bits is not None else rest.split()[0])
        elif tag == "Double":
            bits = double_bits_exact.get(idx)
            const_pool[idx] = ("Double", str(bits) if bits is not None else rest.split()[0])

    bootstrap_methods: dict[int, tuple[str, str]] = {}
    for bsm_idx, (kind, arg_cp, fallback_txt) in bootstrap_methods_raw.items():
        if arg_cp is not None and arg_cp in const_pool and const_pool[arg_cp][0] in ("String", "Utf8"):
            bootstrap_methods[bsm_idx] = (kind, const_pool[arg_cp][1])
        else:
            bootstrap_methods[bsm_idx] = (kind, fallback_txt)

    # Second pass: parse method bodies.
    exc_row_re = re.compile(r"^\s+\d+\s+\d+\s+\d+\s+\S+")
    results: list[DisassembledMethod] = []
    cur_name: str | None = None
    cur_params = ""
    cur_instrs: list[tuple[int, str, str]] = []
    cur_has_exc_table = False
    in_code = False
    in_exc_table = False
    in_switch: tuple[int, str, list[str]] | None = None

    def flush_current() -> None:
        if cur_name is not None and cur_instrs:
            results.append(
                DisassembledMethod(
                    owner_internal=owner_internal,
                    jvm_name=cur_name,
                    descriptor_params=cur_params,
                    raw_instrs=cur_instrs,
                    const_pool=const_pool,
                    bootstrap_methods=bootstrap_methods,
                    has_exception_table=cur_has_exc_table,
                )
            )

    for line in lines:
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
            cur_has_exc_table = False
            in_code = False
            in_exc_table = False
            in_switch = None
            continue
        if clinit_re.match(line):
            flush_current()
            cur_name = f"clinit_{class_file.stem}"
            cur_params = ""
            cur_instrs = []
            cur_has_exc_table = False
            in_code = False
            in_exc_table = False
            in_switch = None
            continue
        if cur_name is None:
            continue
        stripped = line.strip()
        if not in_code and not in_exc_table and line.startswith("  ") and not line.startswith("    ") and stripped.endswith(";"):
            # Unrecognized method/field declaration resets pending method state so a subsequent
            # unmatched method's `Code:` cannot append into `cur_instrs`.
            if not stripped.startswith("descriptor:") and not stripped.startswith("Signature:"):
                flush_current()
                cur_name = None
                cur_instrs = []
                cur_has_exc_table = False
                continue
        if stripped == "Code:":
            in_code = True
            in_exc_table = False
            in_switch = None
            continue
        if in_exc_table:
            if exc_row_re.match(line):
                cur_has_exc_table = True
                continue
            if stripped == "" or stripped == "}" or stripped.startswith(_CODE_SECTION_END_PREFIXES) or not line.startswith("  "):
                in_exc_table = False
            else:
                continue
        if not in_code:
            continue
        if in_switch is not None:
            sw_off, sw_op, sw_lines = in_switch
            if stripped == "}":
                cur_instrs.append((sw_off, sw_op, "\n".join(sw_lines)))
                in_switch = None
            else:
                sw_lines.append(stripped)
            continue
        if stripped == "Exception table:":
            in_code = False
            in_exc_table = True
            continue
        if stripped == "" or stripped == "}" or stripped.startswith(_CODE_SECTION_END_PREFIXES):
            in_code = False
            continue
        im = instr_re.match(line)
        if im:
            off = int(im.group(1))
            op = im.group(2)
            arg = (im.group(3) or "").strip()
            if op in ("tableswitch", "lookupswitch"):
                in_switch = (off, op, [])
            else:
                cur_instrs.append((off, op, arg))

    flush_current()
    return results


def parse_switch_entries(payload: str) -> tuple[list[tuple[int, int]], int]:
    """Parses `(cases, default_offset)` from `tableswitch`/`lookupswitch` body lines."""
    cases: list[tuple[int, int]] = []
    default_off: int | None = None
    for line in payload.splitlines():
        k, sep, v = line.partition(":")
        if not sep:
            raise ValueError(f"Malformed switch line: {line!r}")
        key = k.strip()
        target = int(v.strip())
        if key == "default":
            default_off = target
        else:
            cases.append((int(key), target))
    if default_off is None:
        raise ValueError(f"Missing default target in switch: {payload!r}")
    return cases, default_off


def lift_method(method: DisassembledMethod) -> list[str]:
    """Translates raw `(offset, opcode, arg)` tuples into generic Lean `JvmInstr` strings."""
    if method.has_exception_table:
        raise ValueError(
            f"Method {method.jvm_name} has a non-empty Exception table "
            "(try/catch/finally is outside supported JVM subset)",
        )
    offset_to_idx = {off: idx for idx, (off, _, _) in enumerate(method.raw_instrs)}
    lifted: list[str] = []

    def resolve_target(target_off: int, op_name: str) -> int:
        target_idx = offset_to_idx.get(target_off)
        if target_idx is None:
            raise ValueError(
                f"Branch instruction {op_name} in {method.jvm_name} targets invalid bytecode offset {target_off}",
            )
        return target_idx

    for _, op, arg in method.raw_instrs:
        if op in SIMPLE_OPCODES:
            lifted.append(f".{op}")
        elif op == "return":
            lifted.append(".vreturn")
        elif op == "aconst_null":
            lifted.append(".aconstNull")
        elif op == "fconst_0":
            lifted.append(".fconst 0")
        elif op == "fconst_1":
            lifted.append(".fconst 1065353216")
        elif op == "fconst_2":
            lifted.append(".fconst 1073741824")
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
            cp_m = re.match(r"#(\d+)", arg)
            if cp_m:
                cp_idx = int(cp_m.group(1))
                entry = method.const_pool.get(cp_idx)
                if entry is not None:
                    tag, val = entry
                    if tag == "Integer":
                        lifted.append(f".iconst {to_u32_lit(val)}")
                        continue
                    if tag == "Float":
                        lifted.append(f".fconst {int(val)}")
                        continue
                    if tag == "String":
                        lifted.append(f".ldcStr {lean_str_lit(val)}")
                        continue
            int_m = re.search(r"// int (-?\d+)", arg)
            str_m = re.search(r"// String(?: (.*))?$", arg)
            if int_m:
                lifted.append(f".iconst {to_u32_lit(int_m.group(1))}")
            elif str_m:
                lifted.append(f".ldcStr {lean_str_lit(str_m.group(1) or '')}")
            else:
                raise ValueError(f"Unsupported constant pool entry for {op}: {arg}")
        elif op.startswith("lconst_"):
            lifted.append(f".lconst {op.removeprefix('lconst_')}")
        elif op == "ldc2_w":
            cp_m = re.match(r"#(\d+)", arg)
            if cp_m:
                entry = method.const_pool.get(int(cp_m.group(1)))
                if entry is not None and entry[0] == "Long":
                    lifted.append(f".lconst {to_u64_lit(entry[1])}")
                    continue
                if entry is not None and entry[0] == "Double":
                    lifted.append(f".dconst {int(entry[1])}")
                    continue
            m = re.search(r"// long (-?\d+l?)", arg)
            if not m:
                raise ValueError(f"Unsupported constant pool entry for {op}: {arg}")
            lifted.append(f".lconst {to_u64_lit(m.group(1))}")
        elif op.startswith(("iload", "lload", "aload", "fload", "dload", "istore", "lstore", "astore", "fstore", "dstore")):
            base, _, slot_suffix = op.partition("_")
            slot = int(arg) if slot_suffix in ("", "w") else int(slot_suffix)
            lifted.append(f".{base} {slot}")
        elif op in ("iinc", "iinc_w"):
            idx_str, _, delta_str = arg.partition(",")
            if not _:
                raise ValueError(f"Malformed {op} arg: {arg!r}")
            lifted.append(f".iinc {int(idx_str.strip())} {to_i32_lit(delta_str.strip())}")
        elif op == "goto_w":
            target_idx = resolve_target(int(arg), op)
            lifted.append(f".goto {target_idx}")
        elif op in BRANCH_OPCODES:
            target_idx = resolve_target(int(arg), op)
            lifted.append(f".{op} {target_idx}")
        elif op == "tableswitch":
            cases, default_off = parse_switch_entries(arg)
            low = cases[0][0] if cases else 0
            targets = ", ".join(str(resolve_target(t, op)) for _, t in cases)
            lifted.append(f".tableswitch {to_i32_lit(low)} [{targets}] {resolve_target(default_off, op)}")
        elif op == "lookupswitch":
            cases, default_off = parse_switch_entries(arg)
            pairs = ", ".join(f"({to_i32_lit(k)}, {resolve_target(t, op)})" for k, t in cases)
            lifted.append(f".lookupswitch [{pairs}] {resolve_target(default_off, op)}")
        elif op == "new":
            cls = parse_class_ref(arg)
            lifted.append(f".newClass {lean_str_lit(cls)}")
        elif op == "newarray":
            lifted.append(f".newarray {lean_str_lit(arg.strip())}")
        elif op == "anewarray":
            cls = parse_class_ref(arg)
            lifted.append(f".anewarray {lean_str_lit(cls)}")
        elif op in ("checkcast", "instanceof"):
            cls = parse_class_ref(arg)
            lifted.append(f".{op} {lean_str_lit(cls)}")
        elif op in ("getfield", "putfield", "getstatic", "putstatic"):
            owner, member, desc = parse_field_ref(arg, method.owner_internal)
            lifted.append(f".{op} {lean_str_lit(owner)} {lean_str_lit(member)} {lean_str_lit(desc)}")
        elif op in ("invokestatic", "invokevirtual", "invokespecial", "invokeinterface"):
            owner, member, desc = parse_method_ref(arg, method.owner_internal)
            lifted.append(f".{op} {lean_str_lit(owner)} {lean_str_lit(member)} {lean_str_lit(desc)}")
        elif op == "invokedynamic":
            bsm_idx, member, desc = parse_invokedynamic_ref(arg)
            bsm_kind, bsm_arg = method.bootstrap_methods.get(bsm_idx, (member, ""))
            lifted.append(
                f".invokedynamic {lean_str_lit(bsm_kind)} {lean_str_lit(bsm_arg)} {lean_str_lit(desc)}"
            )
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
    strict: bool = False,
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

    if strict and skipped:
        preview = "; ".join(f"{name}: {reason}" for name, reason in skipped[:5])
        raise ValueError(f"--strict: {len(skipped)} method(s) failed to lift: {preview}")

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
        "--strict",
        action="store_true",
        help="Fail if any method fails to lift instead of skipping it.",
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
        strict=args.strict,
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
