/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.Adjunction
public import ReasLib.CategoryTheory.Limits.FiniteConnected
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Sheafification.AddCommGrp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower shriek for sheaves of abelian groups

This file owns the reusable exactness and coefficient-change API for the canonical sheaf pullback
`u.sheafPullback AddCommGrpCat J K`, viewed as lower shriek on abelian sheaves.  The geometric
hypothesis is expressed first through finite connected limits; pullbacks and equalizers are only a
constructor-facing criterion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.AbelianLowerShriek

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Lower shriek on abelian sheaves is exact when the source site has finite connected limits
and the continuous functor of sites preserves them. -/
@[stacks 04BH "finite-connected-limit form"]
theorem exact_of_preservesFiniteConnectedLimits
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasFiniteConnectedLimits C] [PreservesFiniteConnectedLimits u]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseLeftKanExtension P]
    [HasSheafify K AddCommGrpCat.{w}] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

/-- Lower shriek on abelian sheaves is exact when the source site has pullbacks and equalizers
and the continuous functor of sites preserves them. -/
@[stacks 04BH "pullback and equalizer criterion"]
theorem exact_of_preservesPullbacksAndEqualizers
    (u : C ⥤ D) [u.IsContinuous J K]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasPointwiseLeftKanExtension P]
    [HasSheafify K AddCommGrpCat.{w}] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

/-- Lower shriek on abelian sheaves is exact when the continuous functor of sites is a
right adjoint. -/
@[stacks 08P3 "exactness"]
theorem exact_of_isRightAdjoint
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsRightAdjoint]
    [HasSheafify K AddCommGrpCat.{w}] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

/-- Lower shriek on abelian sheaves is exact when the continuous functor of sites has a
specified left adjoint. -/
@[stacks 08P3 "left-adjoint exactness"]
theorem exact_of_leftAdjoint
    (u : C ⥤ D) (l : D ⥤ C) (adj : l ⊣ u) [u.IsContinuous J K]
    [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, u.op.HasLeftKanExtension P]
    [HasSheafify K AddCommGrpCat.{w}] :
    exactFunctor (Sheaf J AddCommGrpCat.{w}) (Sheaf K AddCommGrpCat.{w})
      (u.sheafPullback AddCommGrpCat.{w} J K) := sorry

/-- When the continuous functor of sites is a right adjoint, forgetting the abelian group
structure commutes canonically with lower shriek under the stated compatibility assumptions
for Kan extensions and sheafification. -/
@[stacks 08P3 "underlying sheaves"]
noncomputable def underlyingIso_of_isRightAdjoint
    (u : C ⥤ D) [u.IsContinuous J K] [u.IsRightAdjoint]
    [HasWeakSheafify K AddCommGrpCat.{w}] [HasWeakSheafify K (Type w)]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget AddCommGrpCat.{w})]
    [(forget AddCommGrpCat.{w}).PreservesLeftKanExtensions u.op]
    [K.PreservesSheafification (forget AddCommGrpCat.{w})] :
    u.sheafPullback AddCommGrpCat.{w} J K ⋙
        sheafCompose K (forget AddCommGrpCat.{w}) ≅
      sheafCompose J (forget AddCommGrpCat.{w}) ⋙
        u.sheafPullback (Type w) J K :=
  Functor.sheafPullback.compSheafComposeIso
    u (forget AddCommGrpCat.{w}) J K

end CategoryTheory.Functor.AbelianLowerShriek

-- The comparison is assembled from canonical Kan-extension and sheafification isomorphisms.
