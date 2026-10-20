/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Topos
import ReasLib.CategoryTheory.Limits.Over.FiniteLimits

/-!
# Sheaf functors on slice sites with specified pullbacks

This leaf exposes the slice-site operations that depend on pullbacks while keeping the
chosen ambient pullback structure explicit.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe uC vC w

namespace CategoryTheory
namespace Over
namespace Site
namespace WithPullbacks

variable {C : Type uC} [Category.{vC} C]
variable {S T : C}

/-- Pullback on slice categories, selected by an explicit ambient pullback structure. -/
noncomputable def pullbackFunctor (h : HasPullbacks C) (f : T ⟶ S) : Over S ⥤ Over T :=
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  Site.pullbackFunctor f

/-- The postcomposition-pullback adjunction selected by an explicit ambient pullback structure. -/
noncomputable def mapPullbackAdjunction (h : HasPullbacks C) (f : T ⟶ S) :
    Site.mapFunctor f ⊣ pullbackFunctor h f :=
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  Site.mapPullbackAdjunction f

/-- Postcomposition between slice sites is cocontinuous. -/
theorem mapFunctor_isCocontinuous (J : GrothendieckTopology C) (f : T ⟶ S) :
    Functor.IsCocontinuous (Site.mapFunctor f) (J.over T) (J.over S) :=
  inferInstance

/-- Pullback selected by explicit ambient pullbacks is continuous between slice sites. -/
theorem pullbackFunctor_isContinuous
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S) :
    Functor.IsContinuous (pullbackFunctor h f) (J.over S) (J.over T) := by
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  change Functor.IsContinuous (Site.pullbackFunctor f) (J.over S) (J.over T)
  infer_instance

namespace DirectImage

/-- The direct image from postcomposition agrees with the continuous presentation from an
explicitly selected pullback functor. -/
noncomputable def pullbackPresentation
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S)
    [Functor.IsCocontinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w,
      (Site.mapFunctor f).op.HasPointwiseRightKanExtension P] :
    Site.directImage J f ≅
      (
       -- Local instance justification (proof-local temporary data): `sheafPushforwardContinuous` accepts continuity only as a typeclass argument.
       letI := pullbackFunctor_isContinuous J h f
       (pullbackFunctor h f).sheafPushforwardContinuous
        (Type w) (J.over S) (J.over T)) :=
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  Site.DirectImage.pullbackPresentation J f

/-- Direct image evaluates at the pullback slice object selected by explicit ambient pullbacks. -/
theorem obj_eq
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S)
    [Functor.IsCocontinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w,
      (Site.mapFunctor f).op.HasPointwiseRightKanExtension P]
    (ℱ : Sheaf (J.over T) (Type w)) (U : Over S) :
    ((Site.directImage J f).obj ℱ).obj.obj (op U) =
      ℱ.obj.obj (op ((pullbackFunctor h f).obj U)) := by
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  exact Site.DirectImage.obj_eq J f ℱ U

end DirectImage

namespace Morphism

/-- The direct image of the bundled slice morphism agrees with the continuous presentation
selected by explicit ambient pullbacks. -/
noncomputable def pushforwardPresentation
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S)
    [Functor.IsContinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [Functor.IsCocontinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Site.mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w,
      (Site.mapFunctor f).op.HasPointwiseRightKanExtension P] :
    (Site.morphismOfTopoi J f).pushforward ≅
      (
       -- Local instance justification (proof-local temporary data): `sheafPushforwardContinuous` accepts continuity only as a typeclass argument.
       letI := pullbackFunctor_isContinuous J h f
       (pullbackFunctor h f).sheafPushforwardContinuous
        (Type w) (J.over S) (J.over T)) :=
  eqToIso (Site.Morphism.pushforward J f) ≪≫ DirectImage.pullbackPresentation J h f

end Morphism

namespace LowerShriek

/-- Lower shriek preserves pullbacks when the ambient pullbacks are supplied explicitly. -/
theorem preservesPullbacks
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S)
    [Functor.IsContinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Site.mapFunctor f).op.HasLeftKanExtension P] :
    PreservesLimitsOfShape WalkingCospan (Site.lowerShriek J f) := by
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  exact Site.LowerShriek.Pullbacks.preservesPullbacks J f

/-- Lower shriek preserves equalizers when the ambient pullbacks are supplied explicitly. -/
theorem preservesEqualizers
    (J : GrothendieckTopology C) (h : HasPullbacks C) (f : T ⟶ S)
    [Functor.IsContinuous (Site.mapFunctor f) (J.over T) (J.over S)]
    [HasWeakSheafify (J.over S) (Type w)]
    [∀ P : (Over T)ᵒᵖ ⥤ Type w, (Site.mapFunctor f).op.HasLeftKanExtension P] :
    PreservesLimitsOfShape WalkingParallelPair (Site.lowerShriek J f) := by
  -- Local instance justification (defeq pin): the explicit HasPullbacks argument selects the upstream pullback construction for this bridge.
  letI := h
  exact Site.LowerShriek.Pullbacks.preservesEqualizers J f

end LowerShriek

end WithPullbacks
end Site
end Over
end CategoryTheory
