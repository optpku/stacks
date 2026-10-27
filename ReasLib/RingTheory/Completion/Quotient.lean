/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

/-!
# Quotients of Complete Local Rings

This leaf records permanence of Noetherian complete local rings under proper
quotients.  The theorem is owned by `IsCompleteLocalRing`, so consumers can
use it directly when constructing a quotient instance.

@stack 0325
-/

universe u

namespace IsAdicComplete

/-- Adic completeness descends to a quotient of a Noetherian ring, for the
image of the defining ideal. -/
@[stacks 0325]
theorem quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (J I : Ideal R) [IsAdicComplete J R] :
    IsAdicComplete (J.map (Ideal.Quotient.mk I)) (R ⧸ I) := by
  apply (IsAdicComplete.map_algebraMap_iff J (R ⧸ I)).mpr
  refine
    { toIsHausdorff := IsHausdorff.of_le_jacobson J (R ⧸ I)
        (IsAdicComplete.le_jacobson_bot J)
      toIsPrecomplete := AdicCompletion.of_surjective_iff.mp ?_ }
  intro x
  let q := (Ideal.Quotient.mkₐ R I).toLinearMap
  obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective J
    (show Function.Surjective q from Ideal.Quotient.mk_surjective) x
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective J R y
  exact ⟨q r, (AdicCompletion.map_of J q r).symm⟩

end IsAdicComplete

namespace IsCompleteLocalRing

/-- Lemma 10.160.2 (1), tag `0325`: a proper quotient of a Noetherian complete
local ring is a complete local ring. -/
@[stacks 0325]
theorem quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    IsCompleteLocalRing (R ⧸ I) := sorry

end IsCompleteLocalRing
