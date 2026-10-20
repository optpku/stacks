/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Common refinements of admissible blowups

A finite family of admissible blowups of a quasi-compact and quasi-separated scheme has a common
admissible refinement whose comparison morphisms are themselves admissible blowups.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite family of blowups admissible over a quasi-compact open subscheme has a common
admissible refinement, and every comparison morphism is admissible over the corresponding
inverse-image open subscheme. -/
theorem exists_isAdmissibleBlowup_common_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : QuasiCompact U.ι)
    {n : ℕ} (Xi : Fin n → Scheme.{u}) (bi : ∀ i : Fin n, Xi i ⟶ X)
    (hbi : ∀ i : Fin n, IsAdmissibleBlowup U (bi i)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
          c ≫ bi i = b ∧ IsAdmissibleBlowup (bi i ⁻¹ᵁ U) c := sorry

end AlgebraicGeometry
