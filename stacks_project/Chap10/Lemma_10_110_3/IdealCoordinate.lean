/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.LocalRing
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor
import StacksCheckRecall

/-!
# Ideal-coordinate support for Lemma 10.110.3

@stack 00OA
-/

@[expose] public section

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

@[stacks 00OA "closed-fiber quotient-map tensor injectivity"]
#check @LinearMap.quotientMapByIdeal_injective_iff_lTensor_injective

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.110.3: in a minimal displayed finite free complex, the differential
sends `maximalIdeal R • Cᵢ₊₁` into `(maximalIdeal R) ^ 2 • Cᵢ`. -/
@[stacks 00OA "quadratic maximal-ideal differential estimate"]
lemma diffAt_mem_maximalSquare_of_entries_mem_maximal
    {e : ℕ} (C : FiniteFreeComplex R e) (i : Fin e)
    (hentry : ∀ a : Fin (C.rank i.succ), ∀ b : Fin (C.rank i.castSucc),
      FiniteFreeComplex.diffEntry C i a b ∈ maximalIdeal R)
    {y : C.term i.succ}
    (hy : y ∈ maximalIdeal R • (⊤ : Submodule R (C.term i.succ))) :
    C.diffAt i y ∈ (maximalIdeal R) ^ 2 • (⊤ : Submodule R (C.term i.castSucc)) := sorry

end
