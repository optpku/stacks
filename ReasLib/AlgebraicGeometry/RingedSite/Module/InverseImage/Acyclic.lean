/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Acyclicity of module inverse image from a site presentation

For a continuous and cocontinuous functor of sites, inverse image of an injective module has
vanishing higher cohomology over every source object.  Total acyclicity is a separate, stronger
conclusion and requires the sheaf lower-shriek functor to preserve pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

universe q z uC vC uD vD w

namespace RingedSite.Cocontinuous.moduleInverseImage

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Lemma 21.37.1 (0D6X): inverse image of an injective module along a continuous and
cocontinuous functor of sites has vanishing cohomology in every positive degree over every
source object. -/
@[stacks 0D6X]
theorem higherCohomology_isZero_of_injective
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (I : SheafOfModules.{max z vC} R) [Injective I]
    [HasSheafify J AddCommGrpCat.{max z vC}]
    [HasExt.{q} (Sheaf J AddCommGrpCat.{max z vC})]
    (U : C) (n : ℕ) :
    IsZero
      (CategoryTheory.Sheaf.cohomologyOverObject.{q, z, vC, uC}
        (J := J)
        ((underlyingAbelianSheafFunctor.{max z vC}
          (source (J := J) (K := K) f R)).obj
          ((RingedSite.Cocontinuous.moduleInverseImage
            (J := J) (K := K) f R).obj I)) U (n + 1)) := sorry

/-- Lemma 21.37.4 (0D6Y): if the sheaf lower-shriek functor associated to a continuous and
cocontinuous functor of sites preserves pullbacks, inverse image of an injective module is
totally acyclic on the source site. -/
@[stacks 0D6Y, instance]
theorem isTotallyAcyclic_of_injective
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) (I : SheafOfModules.{z} R) [Injective I]
    [HasSheafify J AddCommGrpCat.{z}]
    [HasExt.{z} (Sheaf J AddCommGrpCat.{z})]
    [(f.sheafPushforwardContinuous (Type z) J K).IsRightAdjoint]
    [PreservesLimitsOfShape WalkingCospan
      (f.sheafPullback (Type z) J K)] :
    Sheaf.IsTotallyAcyclic
      ((underlyingAbelianSheafFunctor.{z}
        (source (J := J) (K := K) f R)).obj
        ((RingedSite.Cocontinuous.moduleInverseImage
          (J := J) (K := K) f R).obj I)) := sorry

end RingedSite.Cocontinuous.moduleInverseImage
