/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Refinements
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex C)

/- Lemma 12.5.15: a short complex is exact exactly when morphisms into its middle object
which are killed by the second map lift through the first map after an epimorphic refinement. -/
@[stacks 08N5] #check
  (ShortComplex.exact_iff_exact_up_to_refinements S :
    S.Exact ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁),
          π ≫ x₂ = x₁ ≫ S.f)

end CategoryTheory
