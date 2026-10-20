/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.CommonRefinement
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 31.34.4: if `X` is quasi-compact and quasi-separated, `U ⊆ X` is a quasi-compact
open subscheme, and `bᵢ : Xᵢ ⟶ X` is a finite family of `U`-admissible blowups, then there is a
`U`-admissible blowup `b : X' ⟶ X` which factors through every `bᵢ`, and each factor map
`X' ⟶ Xᵢ` is admissible over the inverse-image open of `U` in `Xᵢ`. -/
@[stacks 080N] #check
  (AlgebraicGeometry.exists_isAdmissibleBlowup_common_refinement :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (U : X.Opens), AlgebraicGeometry.QuasiCompact U.ι →
      ∀ {n : ℕ} (Xi : Fin n → AlgebraicGeometry.Scheme.{u})
        (bi : ∀ i : Fin n, Xi i ⟶ X),
        (∀ i : Fin n, AlgebraicGeometry.IsAdmissibleBlowup U (bi i)) →
          ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
            AlgebraicGeometry.IsAdmissibleBlowup U b ∧
              ∀ i : Fin n, ∃ c : X' ⟶ Xi i,
                c ≫ bi i = b ∧
                  AlgebraicGeometry.IsAdmissibleBlowup (bi i ⁻¹ᵁ U) c)
