/*
 * Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */
package lean

import lean.runtime.LeanCtor
import lean.runtime.LeanNat
import lean.runtime.LeanObject
import lean.runtime.LeanString

public object mod_l_Init_Prelude {
    @JvmStatic
    public fun f_UInt64_decEq(a: LeanObject?, b: LeanObject?): LeanObject {
        val aVal = if (a is LeanNat) a.smallVal else (a?.tag?.toLong() ?: 0L)
        val bVal = if (b is LeanNat) b.smallVal else (b?.tag?.toLong() ?: 0L)
        return if (aVal == bVal) LeanNat.ONE else LeanNat.ZERO
    }

    @JvmStatic
    public fun f_Nat_decLe(a: LeanObject?, b: LeanObject?): LeanObject {
        val aVal = if (a is LeanNat) a.smallVal else (a?.tag?.toLong() ?: 0L)
        val bVal = if (b is LeanNat) b.smallVal else (b?.tag?.toLong() ?: 0L)
        return if (aVal <= bVal) LeanNat.ONE else LeanNat.ZERO
    }

    @JvmStatic
    public fun f_Nat_decEq(a: LeanObject?, b: LeanObject?): LeanObject {
        val aVal = if (a is LeanNat) a.smallVal else (a?.tag?.toLong() ?: 0L)
        val bVal = if (b is LeanNat) b.smallVal else (b?.tag?.toLong() ?: 0L)
        return if (aVal == bVal) LeanNat.ONE else LeanNat.ZERO
    }
}

public object mod_l_Init_Data_UInt_BasicAux {
    @JvmStatic
    public fun f_UInt64_ofNat(a: LeanObject?): LeanObject = a ?: LeanNat.ZERO

    @JvmStatic
    public fun f_UInt64_toNat(a: LeanObject?): LeanObject = a ?: LeanNat.ZERO
}

public object mod_l_Init_Data_Option_Basic {
    @JvmStatic
    public fun f_Option_instDecidableEq___redArg(
        eqDec: LeanObject?,
        a: LeanObject?,
        b: LeanObject?,
    ): LeanObject {
        if (a == null && b == null) return LeanNat.ONE
        if (a == null || b == null) return LeanNat.ZERO
        val aCtor = a as? LeanCtor ?: return LeanNat.ZERO
        val bCtor = b as? LeanCtor ?: return LeanNat.ZERO
        if (aCtor.tag != bCtor.tag) return LeanNat.ZERO
        if (aCtor.tag == 0) return LeanNat.ONE // none == none
        val aVal = aCtor.getObj(0)
        val bVal = bCtor.getObj(0)
        return if (aVal == bVal) LeanNat.ONE else LeanNat.ZERO
    }
}

public object mod_l_Init_Data_String_Bootstrap {
    @JvmStatic
    public fun f_String_Internal_length(s: LeanObject?): LeanObject {
        val len = if (s is LeanString) s.byteSize.toLong() else 0L
        return LeanNat.ofLong(len)
    }
}

public object mod_l_Init_Data_Int_Basic {
    @JvmStatic
    public fun f_Int_ofNat(n: LeanObject?): LeanObject = n ?: LeanNat.ZERO
}

public object mod_l_Init_Data_Nat_Bitwise_Basic {
    @JvmStatic
    public fun f_Nat_shiftRight(a: LeanObject?, b: LeanObject?): LeanObject {
        val aVal = if (a is LeanNat) a.smallVal else (a?.tag?.toLong() ?: 0L)
        val bVal = if (b is LeanNat) b.smallVal else (b?.tag?.toLong() ?: 0L)
        return LeanNat.ofLong(aVal ushr bVal.toInt())
    }
}

public object mod_l_Init_Data_Repr {
    @JvmStatic
    public fun f_Repr_addAppParen(a: LeanObject?, b: LeanObject?): LeanObject = a ?: LeanString.of("")

    @JvmStatic
    public fun f_Bool_repr___redArg(b: LeanObject?): LeanObject {
        val isTrue = if (b is LeanNat) b.smallVal != 0L else ((b?.tag ?: 0) != 0)
        return LeanString.of(if (isTrue) "true" else "false")
    }

    @JvmStatic
    public fun f_Nat_reprFast(n: LeanObject?): LeanObject {
        val v = if (n is LeanNat) n.smallVal else 0L
        return LeanString.of(v.toString())
    }

    @JvmStatic
    public fun f_Option_repr___redArg(inst: LeanObject?, opt: LeanObject?, prec: LeanObject?): LeanObject =
        LeanString.of(opt?.toString() ?: "none")
}
