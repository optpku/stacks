/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.CategoryTheory.Monoidal.Bimod.InternalHom
public import ReasLib.CategoryTheory.Monoidal.Bimod.Tensor.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive relative internal Hom functors of bimodules

Relative internal Hom with a fixed bimodule source is additive in its target. This follows at the
generic bimodule level from its adjunction with fixed-source balanced tensor product.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Bimod.InternalHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [monoidalPreadditive : MonoidalPreadditive C]
variable [hasEqualizers : HasEqualizers C] [hasCoequalizers : HasCoequalizers C]
variable [preservesTensorLeft :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X)]
variable [preservesTensorRight :
  ∀ X : C, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X)]
variable {A B : Mon C}

include monoidalPreadditive hasEqualizers hasCoequalizers preservesTensorLeft preservesTensorRight

/-- Relative internal Hom with fixed source is additive in its target module. -/
@[stacks 0FR6 "additive relative internal Hom functor"]
instance functorAdditive (H : RightInternalHom C) (N : Bimod A B) :
    (functor H N).Additive := sorry

/-- Relative internal-Hom postcomposition preserves sums of module morphisms. -/
@[simp]
theorem map_add (H : RightInternalHom C) (N : Bimod A B)
    {L L' : RightModule B} (f g : L ⟶ L') :
    map H N (f + g) = map H N f + map H N g := sorry

variable (H : RightInternalHom C) (N : Bimod A B)

#synth (functor H N).Additive

end CategoryTheory.Bimod.InternalHom

end
