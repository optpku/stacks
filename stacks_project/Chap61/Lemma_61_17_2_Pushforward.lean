/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.Over.Adjunction
public import stacks_project.Chap61.Lemma_61_12_19_Pullback
public import stacks_project.Chap61.Lemma_61_17_1_InverseImage

/-!
# Abelian small and big pro-étale pushforwards

Direct image of abelian sheaves along a morphism of schemes, on the small
pro-étale site and on the big slice site, together with the cartesian
small-to-big comparison.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Direct image of abelian sheaves on small pro-étale sites along `f`, given by
continuous sheaf pushforward along `smallProetalePullback f`. -/
abbrev smallPushforward :
    Sheaf (topology T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology S) AddCommGrpCat.{u + 1} :=
  (smallProetalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology S) (topology T)

/-- The small pro-étale direct image is continuous sheaf pushforward along
`smallProetalePullback`. -/
theorem smallPushforward_eq :
    smallPushforward f =
      (smallProetalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology S) (topology T) := sorry

/-- The small pro-étale direct image evaluates an abelian sheaf on the base change
`U ×_S T`. -/
theorem smallPushforward_obj_obj
    (F : Sheaf (topology T) AddCommGrpCat.{u + 1}) (U : S.ProEt) :
    ((smallPushforward f).obj F).1.obj (op U) =
      F.1.obj (op ((smallProetalePullback f).obj U)) := sorry

/-- Direct image of abelian sheaves on big pro-étale slice sites along `f`, given
by the continuous slice-site pushforward. -/
abbrev bigPushforward [HasPullbacksAlong f] :
    Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} :=
  proetaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f

/-- The big pro-étale direct image is the continuous slice-site pushforward. -/
theorem bigPushforward_eq [HasPullbacksAlong f] :
    bigPushforward f =
      proetaleTopology.overMapPushforward AddCommGrpCat.{u + 1} f := sorry

variable {S' T' : Scheme.{u}} (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
variable (sq : IsPullback g' f' f g)

/-- Relocalization followed by big-slice pullback is continuous for the mixed
small-to-big pro-étale topologies. -/
instance relocalizationCompPullback_isContinuous [HasPullbacksAlong f] :
    Functor.IsContinuous (SmallToBig.relocalizationFunctor g ⋙ Over.pullback f)
      (topology S') (proetaleTopology.over T) :=
  Functor.isContinuous_comp (SmallToBig.relocalizationFunctor g) (Over.pullback f)
    (topology S') (proetaleTopology.over S) (proetaleTopology.over T)

/-- Small pullback followed by relocalization is continuous for the mixed
small-to-big pro-étale topologies. -/
instance smallPullbackCompRelocalization_isContinuous :
    Functor.IsContinuous
      (smallProetalePullback f' ⋙ SmallToBig.relocalizationFunctor g')
      (topology S') (proetaleTopology.over T) :=
  Functor.isContinuous_comp (smallProetalePullback f')
    (SmallToBig.relocalizationFunctor g') (topology S') (topology T')
    (proetaleTopology.over T)

/-- Objectwise cartesian identification `U ×_{S'} T' ≅ U ×_S T` in the big
pro-étale slice over `T`. -/
def pullbackRelocalizationIsoApp [HasPullbacksAlong f] (U : S'.ProEt) :
    (smallProetalePullback f' ⋙ SmallToBig.relocalizationFunctor g').obj U ≅
      (SmallToBig.relocalizationFunctor g ⋙ Over.pullback f).obj U :=
  let inner : IsPullback
      (pullback.snd U.hom f') (pullback.fst U.hom f') f' U.hom :=
    (IsPullback.of_hasPullback U.hom f').flip
  let outer : IsPullback
      (pullback.snd U.hom f' ≫ g') (pullback.fst U.hom f') f (U.hom ≫ g) :=
    inner.paste_horiz sq
  let chosen : IsPullback
      (pullback.snd (U.hom ≫ g) f) (pullback.fst (U.hom ≫ g) f) f (U.hom ≫ g) :=
    (IsPullback.of_hasPullback (U.hom ≫ g) f).flip
  Over.isoMk (outer.isoIsPullback T U.left chosen)
    (outer.isoIsPullback_hom_fst T U.left chosen)

/-- Naturality of the objectwise cartesian identification around a cartesian
square of schemes. -/
theorem pullbackRelocalizationIso_naturality [HasPullbacksAlong f]
    {U V : S'.ProEt} (φ : U ⟶ V) :
    (smallProetalePullback f' ⋙ SmallToBig.relocalizationFunctor g').map φ ≫
        (pullbackRelocalizationIsoApp f g f' g' sq V).hom =
      (pullbackRelocalizationIsoApp f g f' g' sq U).hom ≫
        (SmallToBig.relocalizationFunctor g ⋙ Over.pullback f).map φ := sorry

/-- Pulling a small pro-étale object around a cartesian square agrees with first
viewing it on the big slice and then pulling it back. -/
def pullbackRelocalizationIso [HasPullbacksAlong f] :
    smallProetalePullback f' ⋙ SmallToBig.relocalizationFunctor g' ≅
      SmallToBig.relocalizationFunctor g ⋙ Over.pullback f :=
  NatIso.ofComponents (pullbackRelocalizationIsoApp f g f' g' sq)
    (pullbackRelocalizationIso_naturality f g f' g' sq)

/-- The cartesian identification is objectwise the fibre-product isomorphism. -/
theorem pullbackRelocalizationIso_app_eq [HasPullbacksAlong f] (U : S'.ProEt) :
    (pullbackRelocalizationIso f g f' g' sq).app U =
      pullbackRelocalizationIsoApp f g f' g' sq U := sorry

/-- The mixed small-to-big comparison
`bigPushforward f ⋙ iInverseImage g ≅ iInverseImage g' ⋙ smallPushforward f'`
of a cartesian square, on abelian sheaves. -/
def smallToBigPushforwardIso [HasPullbacksAlong f] :
    bigPushforward f ⋙ iInverseImage g ≅
      iInverseImage g' ⋙ smallPushforward f' :=
  Functor.sheafPushforwardContinuousComp (SmallToBig.relocalizationFunctor g)
      (Over.pullback f) AddCommGrpCat.{u + 1} (topology S')
      (proetaleTopology.over S) (proetaleTopology.over T) ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (pullbackRelocalizationIso f g f' g' sq) AddCommGrpCat.{u + 1}
      (topology S') (topology T') (proetaleTopology.over T)).symm

/-- The mixed small-to-big comparison of a cartesian square is an isomorphism of
abelian sheaf functors. -/
theorem smallToBigPushforwardIso_isIso [HasPullbacksAlong f] :
    IsIso (smallToBigPushforwardIso f g f' g' sq).hom := sorry

end AlgebraicGeometry.Scheme.ProEt

