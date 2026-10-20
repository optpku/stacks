/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Big
public import ReasLib.CategoryTheory.Limits.Over.CartesianSquare
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Pullback
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Base change on chosen pro-étale sites

A cartesian square in a chosen big pro-étale presentation induces the mixed
small-to-big comparison between direct and inverse images, using the chosen
small-site pullback.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace BaseChange

variable {X : ChosenBigProetaleSite.{u, v}}
variable {S S' T T' : X.carrier}

/-- Direct image on chosen small pro-étale sheaves, presented by continuous
base change. -/
abbrev smallDirectImage (f : T ⟶ S) :
    Sheaf (smallTopology X T) (Type w) ⥤ Sheaf (smallTopology X S) (Type w) :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (smallPullback f) (Type w) _
    (smallTopology X S) (smallTopology X T) (smallPullback_isContinuous f)

/-- The small direct image is computed by evaluating on the pulled-back small
site object. -/
theorem smallDirectImage_obj_obj (f : T ⟶ S)
    (𝒢 : Sheaf (smallTopology X T) (Type w)) (U : smallSite X S) :
    ((smallDirectImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallPullback f).obj U)) := rfl

/-- The mixed small-to-big comparison
`Big.directImage f ⋙ SmallToBig.inverseImage g ⟶
SmallToBig.inverseImage g' ⋙ smallDirectImage f'` of a cartesian square. -/
abbrev smallToBigComparison
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    Big.directImage f ⋙ SmallToBig.inverseImage g ⟶
      SmallToBig.inverseImage g' ⋙ smallDirectImage f' :=
  (Functor.isoWhiskerRight (Big.directImageIsoPullbackPresentation f)
      (SmallToBig.inverseImage g) ≪≫
    (@Functor.sheafPushforwardContinuousComp' _ _ _ _ _ _
        (smallPullback f') (SmallToBig.relocalizationFunctor g')
        (SmallToBig.relocalizationFunctor g ⋙ Big.pullback f)
        (Functor.isoWhiskerLeft (smallInclusion X S')
          (@Over.pullbackMapIso _ _ X.hasPullbacks _ _ _ _ f g f' g' sq)) (Type w) _
        (smallTopology X S') (smallTopology X T') (bigTopology X T)
        (smallPullback_isContinuous f') (SmallToBig.relocalizationFunctor_isContinuous g')
        (@Functor.isContinuous_comp _ _ _ _ _ _ (SmallToBig.relocalizationFunctor g)
          (Big.pullback f) (smallTopology X S') (bigTopology X S) (bigTopology X T)
          (SmallToBig.relocalizationFunctor_isContinuous g) (Big.pullback_isContinuous f)) ≪≫
      (@Functor.sheafPushforwardContinuousComp _ _ _ _ _ _
        (SmallToBig.relocalizationFunctor g) (Big.pullback f) (Type w) _
        (smallTopology X S') (bigTopology X S) (bigTopology X T)
        (SmallToBig.relocalizationFunctor_isContinuous g) (Big.pullback_isContinuous f)).symm).symm).hom

/-- The mixed small-to-big comparison of a cartesian square is invertible. -/
theorem smallToBigComparison_isIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    IsIso (smallToBigComparison f g f' g' sq) := by
  unfold smallToBigComparison
  infer_instance

end BaseChange
end AlgebraicGeometry.ChosenBigProetaleSite
