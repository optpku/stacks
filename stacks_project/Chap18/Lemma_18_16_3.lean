/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
import StacksCheckRecall

/-!
# Lemma 18.16.3

Lower shriek on abelian sheaves is exact under the pullback-and-equalizer criterion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseLeftKanExtension P]
variable [HasSheafify K AddCommGrpCat.{w}]

/- Lemma 18.16.3 (04BH): a continuous and cocontinuous functor preserving pullbacks and
equalizers induces an exact lower-shriek functor on abelian sheaves. -/
@[stacks 04BH]
#check (Functor.AbelianLowerShriek.exact_of_preservesPullbacksAndEqualizers u :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K))

end CategoryTheory
