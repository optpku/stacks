module

public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero bimodule morphisms

When the ambient tensor product is additive, the zero carrier map is automatically compatible with
both module actions.  This file supplies the pointwise zero operation used by the canonical
preadditive structure on a fixed bimodule category.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory.Bimod

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C]
variable {A B : Mon C}

/-- The zero bimodule morphism is induced by the zero carrier map. -/
@[stacks 0FSC "zero morphism of bimodule objects"]
instance homZero [MonoidalPreadditive C] {M N : Bimod A B} : Zero (M ⟶ N) where
  zero :=
    { hom := 0
      left_act_hom := sorry
      right_act_hom := sorry }

/-- The carrier map of the zero bimodule morphism is the ambient zero morphism. -/
@[simp]
theorem zero_hom [MonoidalPreadditive C] (M N : Bimod A B) :
    (0 : M ⟶ N).hom = 0 := sorry

end CategoryTheory.Bimod

end
