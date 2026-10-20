/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Underlying
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek.Basic
public import ReasLib.CategoryTheory.Sites.Over.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower shriek for modules on ringed sites

This file has two layers.  For a bundled morphism of ringed sites it names the chosen left
adjoint of module pullback.  For a continuous and cocontinuous site functor it constructs the
module inverse image over the restricted ring sheaf, its lower shriek, and the canonical mate
comparing additive and module lower shriek.  The comparison is controlled by its localized
structure-sheaf components.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z u₁ u₂ v₁ v₂ uX vX uY vY

namespace RingedSite.Hom

section LowerShriek

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : Hom X Y)
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePullback.{z}).IsRightAdjoint]

/-- The module lower-shriek functor is the chosen left adjoint of module pullback. -/
@[stacks 0797 "bundled lower shriek"]
noncomputable abbrev moduleLowerShriek :
    ModuleCat.{z} X ⥤ ModuleCat.{z} Y :=
  f.modulePullback.{z}.leftAdjoint

namespace moduleLowerShriek

/-- The bundled module lower-shriek functor is left adjoint to module pullback. -/
@[stacks 0797 "bundled adjunction"]
noncomputable def adjunction :
    f.moduleLowerShriek ⊣ f.modulePullback.{z} :=
  Adjunction.ofIsRightAdjoint f.modulePullback.{z}

/-- The Hom equivalence induced by the module lower-shriek/pullback adjunction. -/
noncomputable def homEquiv
    (F : ModuleCat.{z} X) (G : ModuleCat.{z} Y) :
    (f.moduleLowerShriek.obj F ⟶ G) ≃
      (F ⟶ f.modulePullback.{z}.obj G) :=
  (adjunction f).homEquiv F G

/-- Module lower shriek is additive, as the left adjoint of additive module pullback. -/
@[stacks 0797 "additive"]
theorem additive : f.moduleLowerShriek.Additive := sorry

end moduleLowerShriek

end LowerShriek

end RingedSite.Hom

namespace RingedSite.Cocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- The inverse-image ring sheaf associated to a continuous site functor. -/
@[stacks 0797 "inverse-image ring sheaf"]
abbrev inverseImageRingSheaf
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) :
    Sheaf J RingCat.{w} :=
  (f.sheafPushforwardContinuous RingCat.{w} J K).obj R

/-- The module inverse-image functor over the restricted ring sheaf.  Its base functor is fixed
explicitly to `f`, so this is not the same-site identity pushforward. -/
@[stacks 0797 "continuous module inverse image"]
noncomputable abbrev moduleInverseImage
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) :
    SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R) :=
  SheafOfModules.pushforward (F := f)
    (𝟙 (inverseImageRingSheaf (J := J) (K := K) f R))

namespace moduleInverseImage

/-- The source ringed site of inverse image along a continuous site functor. -/
@[stacks 07AC "source ringed site"]
abbrev source (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) :=
  RingedSite.ofRingSheaf J
    (inverseImageRingSheaf (J := J) (K := K) f R)

/-- The target ringed site carrying the original ring sheaf. -/
@[stacks 07AC "target ringed site"]
abbrev target (R : Sheaf K RingCat.{w}) :=
  RingedSite.ofRingSheaf K R

/-- For a continuous and cocontinuous functor of sites, module inverse image over the restricted
ring sheaf admits a left adjoint. -/
@[stacks 0797, instance]
theorem isRightAdjoint
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    (moduleInverseImage (J := J) (K := K) f R :
      SheafOfModules.{z} R ⥤
        SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R)).IsRightAdjoint := sorry

end moduleInverseImage

/-- The module lower-shriek functor associated to a continuous and cocontinuous site functor. -/
@[stacks 0797]
noncomputable abbrev moduleLowerShriek
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R) ⥤
      SheafOfModules.{z} R :=
  (moduleInverseImage (J := J) (K := K) f R :
    SheafOfModules.{z} R ⥤
      SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R)).leftAdjoint

namespace moduleLowerShriek

/-- The canonical module lower-shriek/inverse-image adjunction for a continuous and
cocontinuous site functor. -/
@[stacks 0797 "adjunction"]
noncomputable def adjunction
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    (moduleLowerShriek (J := J) (K := K) f R :
      SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R) ⥤
        SheafOfModules.{z} R) ⊣
      (moduleInverseImage (J := J) (K := K) f R :
        SheafOfModules.{z} R ⥤
          SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R)) :=
  Adjunction.ofIsRightAdjoint
    (moduleInverseImage (J := J) (K := K) f R :
      SheafOfModules.{z} R ⥤
        SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R))

/-- The Hom equivalence characterizing lower shriek for a continuous and cocontinuous site
functor. -/
noncomputable def homEquiv
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w})
    (F : SheafOfModules.{z} (inverseImageRingSheaf (J := J) (K := K) f R))
    (G : SheafOfModules.{z} R) :
    ((moduleLowerShriek (J := J) (K := K) f R).obj F ⟶ G) ≃
      (F ⟶ (moduleInverseImage (J := J) (K := K) f R).obj G) :=
  (adjunction
    (J := J) (K := K) f R).homEquiv F G

/-- The lower-shriek functor for a continuous and cocontinuous site functor is additive, as the
left adjoint of the additive module inverse-image functor. -/
@[stacks 0797 "additive"]
theorem additive
    (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
    (R : Sheaf K RingCat.{w}) :
    (moduleLowerShriek (J := J) (K := K) f R).Additive := sorry

end moduleLowerShriek

namespace moduleInverseImage

/-- Forgetting module structure strictly commutes with module inverse image along a continuous
site functor. -/
@[stacks 0798 "right-adjoint square"]
noncomputable def underlyingIso
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) :
    moduleInverseImage (J := J) (K := K) f R ⋙
        SheafOfModules.toSheaf
          (inverseImageRingSheaf (J := J) (K := K) f R) ≅
      SheafOfModules.toSheaf R ⋙
        f.sheafPushforwardContinuous AddCommGrpCat.{z} J K :=
  Iso.refl _

end moduleInverseImage

namespace Localization

/-- The canonical comparison between the localized inverse-image ring sheaf and direct image
from the localized target site. -/
@[stacks 0799 "ring comparison"]
noncomputable def ringIso
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) (U : C) :
    (inverseImageRingSheaf (J := J) (K := K) f R).over U ≅
      (f.sheafPushforwardOverPost (JD := J) (JC := K) U RingCat.{w}).obj
        (R.over (f.obj U)) :=
  (f.sheafPushforwardOverPostComp (JD := J) (JC := K) U RingCat.{w}).symm.app R

/-- The right-adjoint form of the localized structure-sheaf comparison. -/
@[stacks 0799 "right-adjoint form"]
noncomputable def structureSheafRightAdjointMap
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) (U : C) :
    SheafOfModules.Localization.unitUnderlying
        (inverseImageRingSheaf (J := J) (K := K) f R) U ⟶
      (f.sheafPushforwardOverPost (JD := J) (JC := K) U AddCommGrpCat.{w}).obj
        (SheafOfModules.Localization.unitUnderlying R (f.obj U)) :=
  (SheafOfModules.toSheaf
      ((inverseImageRingSheaf (J := J) (K := K) f R).over U)).map
    (SheafOfModules.unitToPushforwardObjUnit
      ((ringIso (J := J) (K := K) f R U).hom))

/-- The canonical localized comparison from additive lower shriek of the inverse-image structure
sheaf to the target localized structure sheaf. -/
@[stacks 0799]
noncomputable def structureSheafComparison
    (f : C ⥤ D) [f.IsContinuous J K] (R : Sheaf K RingCat.{w}) (U : C)
    [HasWeakSheafify (K.over (f.obj U)) AddCommGrpCat.{w}]
    [∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post f).op.HasLeftKanExtension P] :
    ((Over.post f).sheafPullback AddCommGrpCat.{w}
        (J.over U) (K.over (f.obj U))).obj
        (SheafOfModules.Localization.unitUnderlying
          (inverseImageRingSheaf (J := J) (K := K) f R) U) ⟶
      SheafOfModules.Localization.unitUnderlying R (f.obj U) :=
  (((Over.post f).sheafAdjunctionContinuous AddCommGrpCat.{w}
      (J.over U) (K.over (f.obj U))).homEquiv _ _).symm
    (structureSheafRightAdjointMap (J := J) (K := K) f R U)

end Localization

namespace moduleLowerShriek

variable (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{w})

section Comparison

variable [HasWeakSheafify K AddCommGrpCat.{z}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P]

/-- The canonical mate from additive lower shriek after forgetting to forgetting after module lower
shriek. -/
@[stacks 0798 "forgetful comparison"]
noncomputable def underlyingComparison :
    SheafOfModules.toSheaf
        (inverseImageRingSheaf (J := J) (K := K) f R) ⋙
        f.sheafPullback AddCommGrpCat.{z} J K ⟶
      moduleLowerShriek (J := J) (K := K) f R ⋙
        SheafOfModules.toSheaf R :=
  ((mateEquiv
      (adjunction (J := J) (K := K) f R)
      (f.sheafAdjunctionContinuous AddCommGrpCat.{z} J K)).symm
    (moduleInverseImage.underlyingIso (J := J) (K := K) f R).hom).natTrans

end Comparison

variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{w}, f.op.HasLeftKanExtension P]

/-- The forgetful comparison is invertible exactly when all localized structure-sheaf comparisons
are invertible. -/
@[stacks 0798 "localization criterion"]
theorem underlyingComparison_isIso_iff
    [∀ U : C, HasWeakSheafify (K.over (f.obj U)) AddCommGrpCat.{w}]
    [∀ U : C, ∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w},
      (Over.post f).op.HasLeftKanExtension P] :
    IsIso (underlyingComparison (J := J) (K := K) f R) ↔
      ∀ U : C,
        IsIso (Localization.structureSheafComparison (J := J) (K := K) f R U) := sorry

end moduleLowerShriek

namespace moduleLowerShriek

/-- The forgetful comparison for module lower shriek is not uniformly invertible for all continuous
and cocontinuous site functors and ring sheaves. -/
@[stacks 0798 "nonautomatic"]
theorem not_all_underlyingComparison_isIso :
    ¬ ∀ {C : Type u₁} [Category.{v₁} C]
        {D : Type u₂} [Category.{v₂} D]
        {J : GrothendieckTopology C} {K : GrothendieckTopology D}
        (f : C ⥤ D) [f.IsContinuous J K] [f.IsCocontinuous J K]
        (R : Sheaf K RingCat.{w})
        [HasWeakSheafify K AddCommGrpCat.{z}]
        [∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{z}, f.op.HasLeftKanExtension P],
      IsIso (moduleLowerShriek.underlyingComparison
        (J := J) (K := K) f R) := sorry

end moduleLowerShriek

-- `moduleLowerShriek` is the chosen witness owned by the Prop-valued right-adjoint theorem; its
-- adjunction and Hom equivalence are the public specification. Any `sorryAx` reported for that
-- choice comes from the deferred existence/coherence proof, not from a data placeholder here.

end RingedSite.Cocontinuous

namespace RingedSite.Hom

-- The bundled lower shriek is likewise the choice owned by an ambient `IsRightAdjoint` instance,
-- with `moduleLowerShriek.adjunction` and `.homEquiv` exposing its reusable specification.

end RingedSite.Hom
