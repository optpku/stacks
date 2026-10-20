/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree

@[expose] public section

/-!
# Semi-Free Filtration Constructions

This leaf records reusable inputs and closure properties for semi-free
filtrations of cochain complexes of modules.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A cochain complex is a direct sum of shifted free modules when it is isomorphic to a chosen
coproduct of shifted free cochain complexes. -/
def IsDirectSumOfShiftedFree (P : CochainComplex (ModuleCat.{u, u} A) ℤ) : Prop :=
  ∃ (ι : Type u) (degree : ι → ℤ)
    (hι : HasCoproduct (fun i ↦ shiftedFreeDGModule A (degree i))),
      let _ := hι
      Nonempty (P ≅ ∐ fun i ↦ shiftedFreeDGModule A (degree i))

namespace IsDirectSumOfShiftedFree

/-- A direct sum of shifted free cochain complexes admits a semi-free filtration. -/
theorem hasSemiFreeFiltration {P : CochainComplex (ModuleCat.{u, u} A) ℤ}
    (hP : IsDirectSumOfShiftedFree P) :
    HasSemiFreeFiltration P := sorry

end IsDirectSumOfShiftedFree

/-- An admissible short exact sequence with shifted-free end terms gives a semi-free filtration of
its middle term. -/
theorem hasSemiFreeFiltration_of_admissibleShortExact_of_shiftedFree
    (S : ShortComplex (ModuleCat.DGMod A))
    (hS : IsAdmissibleShortExact (dgModuleUnderlyingGradedHomSystem (A := A)) S)
    (hX₁ : IsDirectSumOfShiftedFree S.X₁)
    (hX₃ : IsDirectSumOfShiftedFree S.X₃) :
    HasSemiFreeFiltration S.X₂ := sorry

end CochainComplex
