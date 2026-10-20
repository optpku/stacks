/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Equivalence
public import ReasLib.CategoryTheory.Sites.DenseSubsite.Over

/-!
# Lemma 7.29.3

The dense-subsite construction on slice sites and its sheaf-theoretic
consequence are owned by the reusable dense-subsite API.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Lemma 7.29.3 (03CH): a dense subsite remains dense after passage to the
slice site over any object. -/
@[stacks 03CH] #check @Functor.IsDenseSubsite.overPost

/- The corresponding cocontinuous direct image on type-valued sheaves is an
equivalence once its pointwise right Kan extensions are available. -/
variable (F : C ⥤ D) (X : C) [F.IsDenseSubsite J K]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
  (Over.post F).op.HasPointwiseRightKanExtension P]

#synth
  ((Over.post F).sheafPushforwardCocontinuous (Type (max u₁ u₂ v₁ v₂)) (J.over X)
    (K.over (F.obj X))).IsEquivalence

end CategoryTheory
