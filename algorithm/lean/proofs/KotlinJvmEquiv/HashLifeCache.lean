/-
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
 -/

import Jvm.Proofs
import KotlinJvmBytecode
import models.HashLifeCacheModel
import theorems.HashLifeCacheModelTheorems

namespace Algorithm.KotlinJvmVerification
open Algorithm.KotlinJvmBytecode
open Algorithm.KotlinModel

set_option maxRecDepth 2000

private abbrev CacheVal := Jvm.JvmVal Empty
private abbrev CacheState := Jvm.JvmState Empty Unit

private def initCacheState (slots : List (Nat × CacheVal)) (jh : Jvm.JvmHeap Empty := {}) : CacheState :=
  Jvm.initJvmState slots (.i32 0) () jh

private def cacheCls : String := "com/alexvanyo/composelife/algorithm/Cache"
private def wrapCls : String := "com/alexvanyo/composelife/algorithm/Equivalence$Wrapper"
private def fixedWrapCls : String := "com/alexvanyo/composelife/algorithm/Equivalence$FixedWrapper"
private def reuseWrapCls : String := "com/alexvanyo/composelife/algorithm/Equivalence$ReusableWrapper"

private def cIsSubtype (sub sup : String) : Bool :=
  sub == sup ||
  (sub == fixedWrapCls && sup == wrapCls) ||
  (sub == reuseWrapCls && sup == wrapCls) ||
  (sub == "java/util/LinkedHashMap" && sup == "java/util/Map") ||
  sup == "java/lang/Object"

private def cGetField? (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) : Option CacheVal :=
  match h.get? addr with
  | some obj => obj.getField? cIsSubtype cls field
  | none => none

private def cSetField (h : Jvm.JvmHeap Empty) (addr : Nat) (cls field : String) (v : CacheVal) : Jvm.JvmHeap Empty :=
  match h.get? addr with
  | some obj =>
    match obj.setField cIsSubtype cls field v with
    | some obj' => h.set addr obj'
    | none => h
  | none => h

/-- Extract string key from a `CacheVal` (maps use `.str k` keys in our cache proofs). -/
private def asKeyStr? : CacheVal → Option String
  | .str s => some s
  | _ => none

/-- Read `(k, v)` pairs stored in a `LinkedHashMap` instance (each entry is a `.pair (.str k) v`). -/
def getMapEntries? (h : Jvm.JvmHeap Empty) (mapAddr : Nat) : Option (Array CacheVal) :=
  match cGetField? h mapAddr "java/util/LinkedHashMap" "entries" with
  | some (.heapRef arrAddr) =>
    match h.get? arrAddr with
    | some (.objArray _ elems) => some elems
    | _ => none
  | _ => none

private def setHeapAt (h : Jvm.JvmHeap Empty) (addr : Nat) (obj : Jvm.HeapObj Empty) : Jvm.JvmHeap Empty :=
  { h with objects := Array.mk (h.objects.toList.set addr obj) }

private def setMapEntries (h : Jvm.JvmHeap Empty) (mapAddr : Nat) (elems : Array CacheVal) : Jvm.JvmHeap Empty :=
  match cGetField? h mapAddr "java/util/LinkedHashMap" "entries" with
  | some (.heapRef arrAddr) => setHeapAt h arrAddr (.objArray "java/lang/Object" elems)
  | _ => h

private def mapLookup (elems : Array CacheVal) (k : String) : Option CacheVal :=
  (elems.toList.find? fun e => match e with | .pair (.str ek) _ => ek == k | _ => false).bind fun e =>
    match e with | .pair _ v => some v | _ => none

private def mapPutEntry (elems : Array CacheVal) (k : String) (v : CacheVal) : Array CacheVal :=
  if elems.toList.any (fun e => match e with | .pair (.str ek) _ => ek == k | _ => false) then
    Array.mk (elems.toList.map fun e => match e with | .pair (.str ek) _ => if ek == k then .pair (.str k) v else e | _ => e)
  else
    Array.mk (elems.toList ++ [.pair (.str k) v])

private def mapRemoveKey (elems : Array CacheVal) (k : String) : Array CacheVal :=
  Array.mk (elems.toList.filter fun e => match e with | .pair (.str ek) _ => ek != k | _ => true)

/-- Allocate a `LinkedHashMap` instance on the JVM heap. -/
def allocMap (h : Jvm.JvmHeap Empty) (entries : Array CacheVal := #[]) : Nat × Jvm.JvmHeap Empty :=
  let (arrAddr, h1) := h.alloc (.objArray "java/lang/Object" entries)
  h1.alloc (.instance "java/util/LinkedHashMap" [("entries", .heapRef arrAddr)])

/-- Hooks for `Cache` and `Equivalence.{Wrapper, FixedWrapper, ReusableWrapper}`. -/
def mkCacheHooks
    (loadFn : String → CacheVal := fun k => .str ("loaded:" ++ k))
    (genIndex : UInt64 := 42)
    (permKey : String := "perm")
    (isEqFn : String → String → Bool := fun a b => a == b)
    (hashFn : String → UInt32 := fun s => UInt32.ofNat s.length) :
    Jvm.JvmHooks Empty Unit where
  isSubtypeOf := cIsSubtype
  checkCast cls v :=
    match cls, v with
    | "java/lang/Number", .boxedLong _ => some v
    | "java/util/Map$Entry", .pair _ _ => some v
    | _, _ => Jvm.defaultCheckCast (fun _ a => nomatch a) cls v
  stepNewClass st cls :=
    match cls with
    | "java/util/LinkedHashMap" =>
      let (addr, h') := allocMap st.jvmHeap #[]
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
    | _ =>
      let (addr, h') := st.jvmHeap.alloc (.instance cls [])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef addr :: st.stack, jvmHeap := h' })
  stepInvokeSpecial st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/util/LinkedHashMap", "<init>", "()V", _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "java/lang/IllegalStateException", "<init>", "(Ljava/lang/String;)V", _ :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := rest })
    | "com/alexvanyo/composelife/algorithm/Equivalence$Wrapper", "<init>",
        "(Lcom/alexvanyo/composelife/algorithm/Equivalence;)V", eqRef :: .heapRef addr :: rest =>
      let h' := cSetField st.jvmHeap addr wrapCls "equivalence" eqRef
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h' })
    | "com/alexvanyo/composelife/algorithm/Equivalence$FixedWrapper", "<init>",
        "(Lcom/alexvanyo/composelife/algorithm/Equivalence;Ljava/lang/Object;)V",
        val :: eqRef :: .heapRef addr :: rest =>
      let h1 := cSetField st.jvmHeap addr fixedWrapCls "equivalence" eqRef
      let h2 := cSetField h1 addr fixedWrapCls "value" val
      .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h2 })
    | _, _, _, _ => .inr none
  stepInvokeVirtual st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/lang/Object", "toString", "()Ljava/lang/String;", .str s :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str s :: rest })
    | "java/lang/Number", "longValue", "()J", .boxedLong v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i64 v :: rest })
    | "com/alexvanyo/composelife/algorithm/Equivalence$Wrapper", "getValue", "()Ljava/lang/Object;",
        .heapRef addr :: rest
    | "com/alexvanyo/composelife/algorithm/Equivalence$ReusableWrapper", "getValue", "()Ljava/lang/Object;",
        .heapRef addr :: rest =>
      match cGetField? st.jvmHeap addr wrapCls "value" with
      | some v => .inl (some { st with pc := st.pc + 1, stack := v :: rest })
      | none =>
        match cGetField? st.jvmHeap addr reuseWrapCls "_value" with
        | some v => if v.isNull then .inr none else .inl (some { st with pc := st.pc + 1, stack := v :: rest })
        | none => .inr none
    | "com/alexvanyo/composelife/algorithm/Equivalence$ReusableWrapper",
        "getEquivalence$ComposeLife_algorithm", "()Lcom/alexvanyo/composelife/algorithm/Equivalence;",
        .heapRef addr :: rest =>
      match cGetField? st.jvmHeap addr wrapCls "equivalence" with
      | some eqRef => .inl (some { st with pc := st.pc + 1, stack := eqRef :: rest })
      | none => .inr none
    | _, _, _, _ => .inr none
  stepInvokeInterface st cls method desc :=
    match cls, method, desc, st.stack with
    | "java/util/Map", "get", "(Ljava/lang/Object;)Ljava/lang/Object;", k :: .heapRef mapAddr :: rest =>
      match asKeyStr? k, getMapEntries? st.jvmHeap mapAddr with
      | some ks, some elems =>
        let res := (mapLookup elems ks).getD .null
        .inl (some { st with pc := st.pc + 1, stack := res :: rest })
      | _, _ => .inr none
    | "java/util/Map", "put", "(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;",
        v :: k :: .heapRef mapAddr :: rest =>
      match asKeyStr? k, getMapEntries? st.jvmHeap mapAddr with
      | some ks, some elems =>
        let prev := (mapLookup elems ks).getD .null
        let h' := setMapEntries st.jvmHeap mapAddr (mapPutEntry elems ks v)
        .inl (some { st with pc := st.pc + 1, stack := prev :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "java/util/Map", "remove", "(Ljava/lang/Object;)Ljava/lang/Object;", k :: .heapRef mapAddr :: rest =>
      match asKeyStr? k, getMapEntries? st.jvmHeap mapAddr with
      | some ks, some elems =>
        let prev := (mapLookup elems ks).getD .null
        let h' := setMapEntries st.jvmHeap mapAddr (mapRemoveKey elems ks)
        .inl (some { st with pc := st.pc + 1, stack := prev :: rest, jvmHeap := h' })
      | _, _ => .inr none
    | "java/util/Map", "entrySet", "()Ljava/util/Set;", .heapRef mapAddr :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .heapRef mapAddr :: rest })
    | "java/util/Set", "iterator", "()Ljava/util/Iterator;", .heapRef mapAddr :: rest =>
      let (itAddr, h') := st.jvmHeap.alloc (.instance "MapIter" [("map", .heapRef mapAddr), ("idx", .i32 0), ("lastKey", .null)])
      .inl (some { st with pc := st.pc + 1, stack := .heapRef itAddr :: rest, jvmHeap := h' })
    | "java/util/Iterator", "hasNext", "()Z", .heapRef itAddr :: rest =>
      match cGetField? st.jvmHeap itAddr "MapIter" "map", cGetField? st.jvmHeap itAddr "MapIter" "idx" with
      | some (.heapRef mapAddr), some (.i32 idx) =>
        match getMapEntries? st.jvmHeap mapAddr with
        | some elems =>
          .inl (some { st with pc := st.pc + 1, stack := .i32 (if idx.toNat < elems.size then 1 else 0) :: rest })
        | none => .inr none
      | _, _ => .inr none
    | "java/util/Iterator", "next", "()Ljava/lang/Object;", .heapRef itAddr :: rest =>
      match cGetField? st.jvmHeap itAddr "MapIter" "map", cGetField? st.jvmHeap itAddr "MapIter" "idx" with
      | some (.heapRef mapAddr), some (.i32 idx) =>
        match getMapEntries? st.jvmHeap mapAddr with
        | some elems =>
          match elems[idx.toNat]? with
          | some (.pair k v) =>
            let h' := setHeapAt st.jvmHeap itAddr (.instance "MapIter" [("map", .heapRef mapAddr), ("idx", .i32 (idx + 1)), ("lastKey", k)])
            .inl (some { st with pc := st.pc + 1, stack := .pair k v :: rest, jvmHeap := h' })
          | _ => .inr none
        | none => .inr none
      | _, _ => .inr none
    | "java/util/Iterator", "remove", "()V", .heapRef itAddr :: rest =>
      match cGetField? st.jvmHeap itAddr "MapIter" "map",
            cGetField? st.jvmHeap itAddr "MapIter" "idx",
            cGetField? st.jvmHeap itAddr "MapIter" "lastKey" with
      | some (.heapRef mapAddr), some (.i32 idx), some (.str ks) =>
        match getMapEntries? st.jvmHeap mapAddr with
        | some elems =>
          let h1 := setMapEntries st.jvmHeap mapAddr (mapRemoveKey elems ks)
          let h2 := setHeapAt h1 itAddr (.instance "MapIter" [("map", .heapRef mapAddr), ("idx", .i32 (idx - 1)), ("lastKey", .null)])
          .inl (some { st with pc := st.pc + 1, stack := rest, jvmHeap := h2 })
        | none => .inr none
      | _, _, _ => .inr none
    | "java/util/Map$Entry", "getKey", "()Ljava/lang/Object;", .pair k _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := k :: rest })
    | "java/util/Map$Entry", "getValue", "()Ljava/lang/Object;", .pair _ v :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := v :: rest })
    | "kotlin/jvm/functions/Function1", "invoke", "(Ljava/lang/Object;)Ljava/lang/Object;",
        .str k :: .allocRef "load" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := loadFn k :: rest })
    | "kotlin/jvm/functions/Function0", "invoke", "()Ljava/lang/Object;",
        .allocRef "getGen" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .boxedLong genIndex :: rest })
    | "kotlin/jvm/functions/Function0", "invoke", "()Ljava/lang/Object;",
        .allocRef "createPerm" :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .str permKey :: rest })
    | "com/alexvanyo/composelife/algorithm/Equivalence", "isEquivalent",
        "(Ljava/lang/Object;Ljava/lang/Object;)Z", .str b :: .str a :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (if isEqFn a b then 1 else 0) :: rest })
    | "com/alexvanyo/composelife/algorithm/Equivalence", "hash",
        "(Ljava/lang/Object;)I", .str a :: _ :: rest =>
      .inl (some { st with pc := st.pc + 1, stack := .i32 (hashFn a) :: rest })
    | _, _, _, _ => .inr none

abbrev cacheHooks : Jvm.JvmHooks Empty Unit := mkCacheHooks

/-! ### Cache -/

theorem cache_clinit_equiv :
    Jvm.runJvm cacheHooks 10 Cache_clinit_prog (initCacheState []) = some .unit := rfl

theorem cache_init_equiv :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance cacheCls [])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 40 Cache_init_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .allocRef "load"), (2, .allocRef "getGen")] h) =
        some (.unit, endSt) ∧
      cGetField? endSt.jvmHeap selfAddr cacheCls "mutableMap" = some (.heapRef 2) ∧
      cGetField? endSt.jvmHeap selfAddr cacheCls "lastAccessedGenerationMap" = some (.heapRef 4) :=
  ⟨_, rfl, rfl, rfl⟩

theorem cache_getMap_equiv (m : CacheVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance cacheCls [("mutableMap", m)])
    Jvm.runJvm cacheHooks 10 Cache_getMap_prog (initCacheState [(0, .heapRef selfAddr)] h) = some m := rfl

theorem cache_get_miss_equiv (loadFn : String → String) (gen : UInt64) (k : String) :
    let (mAddr, h0) := allocMap {} #[]
    let (gAddr, h1) := allocMap h0 #[]
    let (selfAddr, h2) := h1.alloc (.instance cacheCls
      [("load", .allocRef "load"), ("getGenerationIndex", .allocRef "getGen"),
       ("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
    ∃ endSt,
      Jvm.runJvmRes (mkCacheHooks (fun s => .str (loadFn s)) gen) 60 Cache_get_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .str k)] h2) = some (.str (loadFn k), endSt) ∧
      getMapEntries? endSt.jvmHeap mAddr = some #[.pair (.str k) (.str (loadFn k))] ∧
      getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str k) (.boxedLong gen)] :=
  ⟨_, rfl, rfl, rfl⟩

theorem cache_getWithQuery_hit_equiv (gen : UInt64) (v : String) :
    let (mAddr, h0) := allocMap {} #[.pair (.str "k") (.str v)]
    let (gAddr, h1) := allocMap h0 #[.pair (.str "k") (.boxedLong 0)]
    let (selfAddr, h2) := h1.alloc (.instance cacheCls
      [("load", .allocRef "load"), ("getGenerationIndex", .allocRef "getGen"),
       ("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
    ∃ endSt,
      Jvm.runJvmRes (mkCacheHooks (genIndex := gen)) 60 Cache_getWithQuery_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .str "k"), (2, .allocRef "createPerm")] h2) =
        some (.str v, endSt) ∧
      getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str "k") (.boxedLong gen)] :=
  ⟨_, rfl, rfl⟩

theorem cache_getWithQuery_miss_equiv (loadFn : String → CacheVal) (gen : UInt64) (qKey pKey : String) :
    let (mAddr, h0) := allocMap {} #[]
    let (gAddr, h1) := allocMap h0 #[]
    let (selfAddr, h2) := h1.alloc (.instance cacheCls
      [("load", .allocRef "load"), ("getGenerationIndex", .allocRef "getGen"),
       ("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
    ∃ endSt,
      Jvm.runJvmRes (mkCacheHooks loadFn gen pKey) 80 Cache_getWithQuery_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .str qKey), (2, .allocRef "createPerm")] h2) =
        some (loadFn pKey, endSt) ∧
      getMapEntries? endSt.jvmHeap mAddr = some #[.pair (.str pKey) (loadFn pKey)] ∧
      getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str pKey) (.boxedLong gen)] :=
  ⟨_, rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
theorem cache_prune_evicts_old_equiv (v : String) :
    let (mAddr, h0) := allocMap {} #[.pair (.str "k") (.str v)]
    let (gAddr, h1) := allocMap h0 #[.pair (.str "k") (.boxedLong 5)]
    let (selfAddr, h2) := h1.alloc (.instance cacheCls
      [("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 40 Cache_prune_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .i64 10)] h2) = some (.unit, endSt) ∧
      getMapEntries? endSt.jvmHeap mAddr = some #[] ∧
      getMapEntries? endSt.jvmHeap gAddr = some #[] := by
  have hfast :
      let (mAddr, h0) := allocMap {} #[.pair (.str "k") (.str v)]
      let (gAddr, h1) := allocMap h0 #[.pair (.str "k") (.boxedLong 5)]
      let (selfAddr, h2) := h1.alloc (.instance cacheCls
        [("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
      ∃ endSt,
        Jvm.runJvmResFast cacheHooks 40 Cache_prune_prog 0 Cache_prune_prog
          (initCacheState [(0, .heapRef selfAddr), (1, .i64 10)] h2) = some (.unit, endSt) ∧
        getMapEntries? endSt.jvmHeap mAddr = some #[] ∧
        getMapEntries? endSt.jvmHeap gAddr = some #[] :=
    ⟨_, rfl, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨endSt, hrun, hm, hg⟩
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 cacheHooks 40 _ _ _ rfl hrun, hm, hg⟩

set_option maxHeartbeats 400000 in
theorem cache_prune_retains_recent_equiv (v : CacheVal) :
    let (mAddr, h0) := allocMap {} #[.pair (.str "k") v]
    let (gAddr, h1) := allocMap h0 #[.pair (.str "k") (.boxedLong 15)]
    let (selfAddr, h2) := h1.alloc (.instance cacheCls
      [("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 40 Cache_prune_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .i64 10)] h2) = some (.unit, endSt) ∧
      getMapEntries? endSt.jvmHeap mAddr = some #[.pair (.str "k") v] ∧
      getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str "k") (.boxedLong 15)] := by
  have hfast :
      let (mAddr, h0) := allocMap {} #[.pair (.str "k") v]
      let (gAddr, h1) := allocMap h0 #[.pair (.str "k") (.boxedLong 15)]
      let (selfAddr, h2) := h1.alloc (.instance cacheCls
        [("mutableMap", .heapRef mAddr), ("lastAccessedGenerationMap", .heapRef gAddr)])
      ∃ endSt,
        Jvm.runJvmResFast cacheHooks 40 Cache_prune_prog 0 Cache_prune_prog
          (initCacheState [(0, .heapRef selfAddr), (1, .i64 10)] h2) = some (.unit, endSt) ∧
        getMapEntries? endSt.jvmHeap mAddr = some #[.pair (.str "k") v] ∧
        getMapEntries? endSt.jvmHeap gAddr = some #[.pair (.str "k") (.boxedLong 15)] :=
    ⟨_, rfl, rfl, rfl⟩
  dsimp only at hfast ⊢
  rcases hfast with ⟨endSt, hrun, hm, hg⟩
  exact ⟨endSt, Jvm.runJvmRes_of_runJvmResFast0 cacheHooks 40 _ _ _ rfl hrun, hm, hg⟩

/-! ### Equivalence.Wrapper, FixedWrapper, ReusableWrapper -/

theorem equivalence_wrapper_clinit_equiv :
    Jvm.runJvm cacheHooks 10 Equivalence_Wrapper_clinit_prog (initCacheState []) = some .unit := rfl

theorem equivalence_wrapper_init_equiv (eqRef : CacheVal) (hnn : eqRef.isNull = false) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance wrapCls [])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 20 Equivalence_Wrapper_init_prog
        (initCacheState [(0, .heapRef selfAddr), (1, eqRef)] h) = some (.unit, endSt) ∧
      cGetField? endSt.jvmHeap selfAddr wrapCls "equivalence" = some eqRef := by
  cases eqRef <;> simp_all [Jvm.JvmVal.isNull] <;> exact ⟨_, rfl, rfl⟩

theorem equivalence_wrapper_getEquivalence_equiv (eqRef : CacheVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance wrapCls [("equivalence", eqRef)])
    Jvm.runJvm cacheHooks 10 Equivalence_Wrapper_getEquivalence_ComposeLife_algorithm_prog
      (initCacheState [(0, .heapRef selfAddr)] h) = some eqRef := rfl

theorem equivalence_wrapper_equals_sameEq_equiv
    (res : Bool) (a b : String) :
    let (eq1, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "com/alexvanyo/composelife/algorithm/Equivalence" [])
    let (w1, h1) := h0.alloc (.instance fixedWrapCls [("equivalence", .heapRef eq1), ("value", .str a)])
    let (w2, h2) := h1.alloc (.instance fixedWrapCls [("equivalence", .heapRef eq1), ("value", .str b)])
    Jvm.runJvm (mkCacheHooks (isEqFn := fun _ _ => res)) 40 Equivalence_Wrapper_equals_prog
      (initCacheState [(0, .heapRef w1), (1, .heapRef w2)] h2) =
      some (.i32 (if res then 1 else 0)) := by
  apply Jvm.runJvm_of_runJvmValFast0 _
    (fun v t e => by dsimp only [mkCacheHooks]; cases v.asI32? with | none => rfl | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl)
    (fun v t e => by dsimp only [mkCacheHooks]; cases v.asI32? with | none => rfl | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl)
    40 _ _ _ rfl
  cases res <;> rfl

theorem equivalence_wrapper_equals_diffEq_false (a b : String) :
    let (eq1, h0) := ({} : Jvm.JvmHeap Empty).alloc (.instance "com/alexvanyo/composelife/algorithm/Equivalence" [])
    let (eq2, h1) := h0.alloc (.instance "com/alexvanyo/composelife/algorithm/Equivalence" [])
    let (w1, h2) := h1.alloc (.instance fixedWrapCls [("equivalence", .heapRef eq1), ("value", .str a)])
    let (w2, h3) := h2.alloc (.instance fixedWrapCls [("equivalence", .heapRef eq2), ("value", .str b)])
    Jvm.runJvm cacheHooks 40 Equivalence_Wrapper_equals_prog
      (initCacheState [(0, .heapRef w1), (1, .heapRef w2)] h3) = some (.i32 0) :=
  Jvm.runJvm_of_runJvmValFast0 _
    (fun v t e => by dsimp only [cacheHooks, mkCacheHooks]; cases v.asI32? with | none => rfl | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl)
    (fun v t e => by dsimp only [cacheHooks, mkCacheHooks]; cases v.asI32? with | none => rfl | some x => cases h : (x == 0) <;> simp [h, Jvm.defaultIteVal] <;> split <;> rfl)
    40 _ _ _ rfl rfl

theorem equivalence_wrapper_hashCode_equiv (hashFn : String → UInt32) (a : String) :
    let (w1, h0) := ({} : Jvm.JvmHeap Empty).alloc
      (.instance fixedWrapCls [("equivalence", .allocRef "eq1"), ("value", .str a)])
    Jvm.runJvm (mkCacheHooks (hashFn := hashFn)) 20 Equivalence_Wrapper_hashCode_prog
      (initCacheState [(0, .heapRef w1)] h0) = some (.i32 (hashFn a)) := rfl

theorem equivalence_fixedWrapper_clinit_equiv :
    Jvm.runJvm cacheHooks 10 Equivalence_FixedWrapper_clinit_prog (initCacheState []) = some .unit := rfl

theorem equivalence_fixedWrapper_init_equiv (v : CacheVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance fixedWrapCls [])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 25 Equivalence_FixedWrapper_init_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .allocRef "eq1"), (2, v)] h) =
        some (.unit, endSt) ∧
      cGetField? endSt.jvmHeap selfAddr fixedWrapCls "value" = some v :=
  ⟨_, rfl, rfl⟩

theorem equivalence_fixedWrapper_getValue_equiv (v : CacheVal) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance fixedWrapCls [("value", v)])
    Jvm.runJvm cacheHooks 10 Equivalence_FixedWrapper_getValue_prog
      (initCacheState [(0, .heapRef selfAddr)] h) = some v := rfl

theorem equivalence_reusableWrapper_clinit_equiv :
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 10 Equivalence_ReusableWrapper_clinit_prog (initCacheState []) =
        some (.unit, endSt) ∧
      endSt.jvmHeap.getStatic? reuseWrapCls "$stable" = some (.i32 8) :=
  ⟨_, rfl, rfl⟩

theorem equivalence_reusableWrapper_init_equiv :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance reuseWrapCls [])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 20 Equivalence_ReusableWrapper_init_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .allocRef "eq1")] h) = some (.unit, endSt) ∧
      cGetField? endSt.jvmHeap selfAddr wrapCls "equivalence" = some (.allocRef "eq1") :=
  ⟨_, rfl, rfl⟩

theorem equivalence_reusableWrapper_getValue_uninit_throws :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance reuseWrapCls [("_value", .null)])
    Jvm.runJvm cacheHooks 30 Equivalence_ReusableWrapper_getValue_prog
      (initCacheState [(0, .heapRef selfAddr)] h) = none := rfl

theorem equivalence_reusableWrapper_getValue_init_equiv (s : String) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance reuseWrapCls [("_value", .str s)])
    Jvm.runJvm cacheHooks 20 Equivalence_ReusableWrapper_getValue_prog
      (initCacheState [(0, .heapRef selfAddr)] h) = some (.str s) := rfl

theorem equivalence_reusableWrapper_set_equiv (s : String) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc (.instance reuseWrapCls [("_value", .null)])
    ∃ endSt,
      Jvm.runJvmRes cacheHooks 20 Equivalence_ReusableWrapper_set_prog
        (initCacheState [(0, .heapRef selfAddr), (1, .str s)] h) = some (.heapRef selfAddr, endSt) ∧
      cGetField? endSt.jvmHeap selfAddr reuseWrapCls "_value" = some (.str s) :=
  ⟨_, rfl, rfl⟩

theorem equivalence_reusableWrapper_toPermanentWrapper_equiv (s : String) :
    let (selfAddr, h) := ({} : Jvm.JvmHeap Empty).alloc
      (.instance reuseWrapCls [("equivalence", .allocRef "eq1"), ("_value", .str s)])
    ∃ fixedAddr endSt,
      Jvm.runJvmRes cacheHooks 25 Equivalence_ReusableWrapper_toPermanentWrapper_prog
        (initCacheState [(0, .heapRef selfAddr)] h) = some (.heapRef fixedAddr, endSt) ∧
      cGetField? endSt.jvmHeap fixedAddr fixedWrapCls "value" = some (.str s) :=
  ⟨1, _, rfl, rfl⟩

end Algorithm.KotlinJvmVerification
