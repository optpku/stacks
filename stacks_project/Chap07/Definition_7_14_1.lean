/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.ExactMorphismOfSites
import StacksCheckRecall

@[expose] public section

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits

/- Definition 7.14.1: a morphism of sites is given by a continuous functor whose sheaf pullback is exact. -/
@[stacks 00X1] #check
  (CategoryTheory.IsExactMorphismOfSites :
    ∀ {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
      [HasWeakSheafify K (Type w)]
      [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasLeftKanExtension P], Prop)
