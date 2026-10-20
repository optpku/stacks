/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Ring properties of locally constant functions -/

@[expose] public section

namespace LocallyConstant

/-- Locally constant functions into a reduced semiring form a reduced semiring. -/
instance instIsReduced (X R : Type*) [TopologicalSpace X] [Semiring R] [IsReduced R] :
    IsReduced (LocallyConstant X R) :=
  isReduced_of_injective (coeFnRingHom : LocallyConstant X R →+* X → R)
    DFunLike.coe_injective

/-- The ring of locally constant functions into a field has Krull dimension at most zero. -/
instance instKrullDimLE_zero (X K : Type*) [TopologicalSpace X] [Field K] :
    Ring.KrullDimLE 0 (LocallyConstant X K) := sorry

end LocallyConstant
