/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Total
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w x

/- Lemma 50.21.1
For qcqs schemes there is a unique pullback-natural multiplicative total
Chern class on `K₀(Vect(X))` whose degree-`i` component lies in
`H_dR^(2i)(X/ℤ)` and whose value on a line bundle is `1 + c₁ᵈᴿ`.
This is the realization of the unique total Chern class for a graded cohomology theory. -/
@[stacks 0FW9] #check
  (AlgebraicGeometry.ChernClass.existsUniqueTotalChernClass :
    ∀ {C : Type u} [Category.{v} C] (toScheme : C ⥤ AlgebraicGeometry.Scheme.{w})
      (A : Cᵒᵖ ⥤ RingCat.{x})
      (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Agrade X)]
      (S : AlgebraicGeometry.ChernClass.CohomologyTheory toScheme A Agrade),
      ∃ c : AlgebraicGeometry.ChernClass.TotalChernClass
          toScheme A Agrade S.firstChernClass,
        ∀ c', c' = c)
