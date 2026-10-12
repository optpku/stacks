/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap61.Lemma_61_12_12_SmallToBig
public import stacks_project.Chap61.Lemma_61_12_15_Big
public import stacks_project.Chap61.Lemma_61_12_16_Pullback
public import ReasLib.CategoryTheory.Sites.Over.BaseChange
public import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Base change on chosen pro-étale sites

A cartesian square in a chosen big pro-étale presentation induces the mixed
small-to-big comparison between direct and inverse images, using the chosen
small-site pullback from Lemma 61.12.16.
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
  (smallPullback f).sheafPushforwardContinuous (Type w)
    (smallTopology X S) (smallTopology X T)

/-- The small direct image is computed by evaluating on the pulled-back small
site object. -/
theorem smallDirectImage_obj_obj (f : T ⟶ S)
    (𝒢 : Sheaf (smallTopology X T) (Type w)) (U : smallSite X S) :
    ((smallDirectImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((smallPullback f).obj U)) := sorry

/-- Objectwise cartesian identification `U' ×[S'] T' ≅ U' ×[S] T` in the
chosen big slice over `T`. -/
def pullbackRelocalizationIsoApp
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) (U : smallSite X S') :
    (smallPullback f' ⋙ SmallToBig.relocalizationFunctor g').obj U ≅
      (SmallToBig.relocalizationFunctor g ⋙ Big.pullback f).obj U :=
  let inner : IsPullback
      (pullback.snd U.obj.hom f') (pullback.fst U.obj.hom f') f' U.obj.hom :=
    (IsPullback.of_hasPullback U.obj.hom f').flip
  let outer : IsPullback
      (pullback.snd U.obj.hom f' ≫ g') (pullback.fst U.obj.hom f') f
        (U.obj.hom ≫ g) :=
    inner.paste_horiz sq
  let chosen : IsPullback
      (pullback.snd (U.obj.hom ≫ g) f) (pullback.fst (U.obj.hom ≫ g) f)
        f (U.obj.hom ≫ g) :=
    (IsPullback.of_hasPullback (U.obj.hom ≫ g) f).flip
  Over.isoMk (outer.isoIsPullback T U.obj.left chosen)
    (outer.isoIsPullback_hom_fst T U.obj.left chosen)

/-- Naturality of the objectwise cartesian identification around a chosen
cartesian square. -/
theorem pullbackRelocalizationIso_naturality
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) {U V : smallSite X S'} (φ : U ⟶ V) :
    (smallPullback f' ⋙ SmallToBig.relocalizationFunctor g').map φ ≫
        (pullbackRelocalizationIsoApp f g f' g' sq V).hom =
      (pullbackRelocalizationIsoApp f g f' g' sq U).hom ≫
        (SmallToBig.relocalizationFunctor g ⋙ Big.pullback f).map φ := sorry

/-- Pulling a small object around a cartesian square agrees with first viewing
it on the big slice and then pulling it back. -/
def pullbackRelocalizationIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    smallPullback f' ⋙ SmallToBig.relocalizationFunctor g' ≅
      SmallToBig.relocalizationFunctor g ⋙ Big.pullback f :=
  NatIso.ofComponents (pullbackRelocalizationIsoApp f g f' g' sq)
    (pullbackRelocalizationIso_naturality f g f' g' sq)

/-- Relocalization followed by big-slice pullback is continuous for the mixed
small-to-big topologies. -/
instance relocalizationCompPullback_isContinuous (f : T ⟶ S) (g : S' ⟶ S) :
    Functor.IsContinuous
      (SmallToBig.relocalizationFunctor g ⋙ Big.pullback f)
      (smallTopology X S') (bigTopology X T) :=
  Functor.isContinuous_comp (SmallToBig.relocalizationFunctor g)
    (Big.pullback f) (smallTopology X S') (bigTopology X S) (bigTopology X T)

/-- The mixed small-to-big comparison
`Big.directImage f ⋙ SmallToBig.inverseImage g ⟶
SmallToBig.inverseImage g' ⋙ smallDirectImage f'` of a cartesian square. -/
def smallToBigComparison
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    Big.directImage f ⋙ SmallToBig.inverseImage g ⟶
      SmallToBig.inverseImage g' ⋙ smallDirectImage f' :=
  (Functor.isoWhiskerRight (Big.directImageIsoPullbackPresentation f)
      (SmallToBig.inverseImage g) ≪≫
    (Functor.sheafPushforwardContinuousComp'
        (pullbackRelocalizationIso f g f' g' sq) (Type w)
        (smallTopology X S') (smallTopology X T') (bigTopology X T) ≪≫
      (Functor.sheafPushforwardContinuousComp
        (SmallToBig.relocalizationFunctor g) (Big.pullback f) (Type w)
        (smallTopology X S') (bigTopology X S) (bigTopology X T)).symm).symm).hom

/-- The mixed small-to-big comparison of a cartesian square is invertible. -/
instance smallToBigComparison_isIso
    (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g) :
    IsIso (smallToBigComparison f g f' g' sq) := sorry

end BaseChange
end AlgebraicGeometry.ChosenBigProetaleSite
