module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square.Exact
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_21_3
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.«69_3_0_1_HigherDirectImage»
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec

/-!
# Flat base change for higher direct images on algebraic spaces

A cartesian square of algebraic spaces with flat bottom edge induces a canonical comparison
`g^* R^i f_* ℱ ⟶ R^i f'_* ((g')^* ℱ)` of sheaves of modules, obtained as the degree-`i`
cohomology of the exact-horizontal derived base-change transformation of Cohomology on Sites
21.15.1: the underived mate is postcomposed by exact pullback along `g`, then compared on the
target by the one-way map `R((g')^* f'_*) ⟶ (g')^* R f'_*`. Under quasi-compactness and
quasi-separatedness of `f` and quasi-coherence of `ℱ`, this map is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The standard derived category of sheaves of modules on an algebraic space. -/
noncomputable instance modulesHasDerivedCategory (X : AlgebraicSpace S)
    [Abelian X.Modules] :
    HasDerivedCategory X.Modules :=
  HasDerivedCategory.standard X.Modules

/-- Module pullback along a flat morphism of algebraic spaces is additive. -/
instance pullback_additive {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (pullback φ).Additive :=
  sorry

/-- Module pullback along a flat morphism of algebraic spaces preserves homology. -/
instance pullback_preservesHomology {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (pullback φ).PreservesHomology :=
  sorry

/-- Module pullback along a flat morphism of algebraic spaces preserves finite limits. -/
instance pullback_preservesFiniteLimits_of_isFlat {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    PreservesFiniteLimits (pullback φ) :=
  sorry

/-- Module pullback along a flat morphism of algebraic spaces preserves finite colimits. -/
instance pullback_preservesFiniteColimits_of_isFlat {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    PreservesFiniteColimits (pullback φ) :=
  sorry

/-- Flat module pullback as a bundled exact functor. -/
def exactPullback {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    Y.Modules ⥤ₑ X.Modules :=
  ExactFunctor.of (pullback φ)

/-- The underlying functor of `exactPullback` is module pullback. -/
theorem exactPullback_obj {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (exactPullback φ).obj = pullback φ :=
  rfl

/-- Algebraic-space module categories with injective resolutions have enough injectives. -/
instance modules_enoughInjectives {X : AlgebraicSpace S} [Abelian X.Modules]
    [HasInjectiveResolutions X.Modules] :
    EnoughInjectives X.Modules :=
  sorry

/-- Module pushforward along a flat morphism of algebraic spaces preserves injective objects. -/
instance pushforward_preservesInjectiveObjects {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (pushforward φ).PreservesInjectiveObjects :=
  sorry

/-- Base change of schemes étale over `Z` along `f ≫ g` identifies with base change along `g`
followed by spaces-étale pullback along `f`. -/
def etaleBaseChangeComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    etaleBaseChange (f ≫ g) ≅ etaleBaseChange g ⋙ spacesEtalePullback f :=
  (smallEtaleInclusion_comp_spacesEtalePullback (f ≫ g)).symm ≪≫
    isoWhiskerLeft (smallEtaleInclusion Z) (spacesEtalePullbackComp f g) ≪≫
    isoWhiskerRight (smallEtaleInclusion_comp_spacesEtalePullback g) (spacesEtalePullback f)

/-- Type-valued direct image along `f`, rewritten through spaces-étale pullback. -/
def typePushforwardFactor {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    typePushforward f ≅
      (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
          (smallEtaleTopology X) (spacesEtaleTopology X) ⋙
        (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
        (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
          (smallEtaleTopology Y) (spacesEtaleTopology Y) :=
  isoWhiskerLeft
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X))
    ((sheafPushforwardContinuousIso (smallEtaleInclusion_comp_spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology X)).symm ≪≫
      sheafPushforwardContinuousComp (smallEtaleInclusion Y) (spacesEtalePullback f)
        (Type u) (smallEtaleTopology Y) (spacesEtaleTopology Y) (spacesEtaleTopology X))

/-- The small étale inclusion is cover-dense in the spaces étale topology. -/
instance smallEtaleInclusion_isCoverDense (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y) :=
  sorry

/-- Spaces-étale pullback along a composite is continuous because each factor is. -/
instance spacesEtalePullback_comp_isContinuous {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback g ⋙ spacesEtalePullback f).IsContinuous
      (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  Functor.isContinuous_comp (spacesEtalePullback g) (spacesEtalePullback f)
    (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X)

/-- Restricting a spaces étale sheaf to the small étale site and extending it back is
isomorphic to the identity. -/
def smallEtaleInclusionContinuousCocontinuousIso (Y : AlgebraicSpace S) :
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ⋙
      (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
        (smallEtaleTopology Y) (spacesEtaleTopology Y) ≅
    𝟭 (Sheaf (spacesEtaleTopology Y) (Type u)) :=
  let restrict :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let extend :=
    (smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let adj :=
    (smallEtaleInclusion Y).sheafAdjunctionCocontinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  NatIso.ofComponents
    (fun F ↦
      let eSmall : restrict.obj ((restrict ⋙ extend).obj F) ≅ restrict.obj F :=
        { hom := adj.counit.app (restrict.obj F)
          inv := restrict.map (adj.unit.app F)
          hom_inv_id := sorry
          inv_hom_id := sorry }
      let i :
          (smallEtaleInclusion Y).op ⋙ ((restrict ⋙ extend).obj F).obj ≅
            (smallEtaleInclusion Y).op ⋙ F.obj :=
        { hom := eSmall.hom.hom
          inv := eSmall.inv.hom
          hom_inv_id := sorry
          inv_hom_id := sorry }
      Functor.IsCoverDense.Types.sheafIso i)
    sorry

/-- Type-valued continuous pushforward along spaces-étale pullback respects composition. -/
def spacesEtaleTypePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Y) (spacesEtaleTopology X) ⋙
      (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology Y) ≅
      (spacesEtalePullback (f ≫ g)).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) (spacesEtaleTopology X) :=
  (spacesEtalePullback g).sheafPushforwardContinuousComp (spacesEtalePullback f) (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y) (spacesEtaleTopology X) ≪≫
    sheafPushforwardContinuousIso (spacesEtalePullbackComp f g).symm (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology X)

/-- Type-valued direct image along a composite is the composite of the type-valued direct
images. -/
def typePushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    typePushforward f ⋙ typePushforward g ≅ typePushforward (f ≫ g) :=
  let iX :=
    (smallEtaleInclusion X).sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)
  let pF :=
    (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let iY :=
    (smallEtaleInclusion Y).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Y) (spacesEtaleTopology Y)
  let pG :=
    (spacesEtalePullback g).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z) (spacesEtaleTopology Y)
  let iZ :=
    (smallEtaleInclusion Z).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology Z) (spacesEtaleTopology Z)
  isoWhiskerRight (typePushforwardFactor f) (typePushforward g) ≪≫
    Functor.associator iX (pF ⋙ iY) (typePushforward g) ≪≫
    isoWhiskerLeft iX (Functor.associator pF iY (typePushforward g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF) (isoWhiskerLeft iY (typePushforwardFactor g)) ≪≫
    isoWhiskerLeft (iX ⋙ pF)
      (Functor.associator iY
          ((smallEtaleInclusion Y).sheafPushforwardCocontinuous (Type u)
            (smallEtaleTopology Y) (spacesEtaleTopology Y))
          (pG ⋙ iZ) ≪≫
        isoWhiskerRight (smallEtaleInclusionContinuousCocontinuousIso Y) (pG ⋙ iZ) ≪≫
        Functor.leftUnitor (pG ⋙ iZ)) ≪≫
    isoWhiskerLeft iX
      (Functor.associator pF pG iZ ≪≫
        isoWhiskerRight (spacesEtaleTypePushforwardComp f g) iZ) ≪≫
    (typePushforwardFactor (f ≫ g)).symm

/-- The underlying type-valued sheaf of an iterated module pushforward. -/
def pushforwardCompForgetIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward f ⋙ pushforward g) ⋙
        Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z) ≅
      Sheaf.InternalModule.ToInternal.underlying (structureSheaf X) ⋙
        typePushforward f ⋙ typePushforward g :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward f)
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f))
      (typePushforward g) ≪≫
    Functor.associator _ _ _

/-- The underlying type-valued comparison of iterated module pushforward with pushforward
along the composite. -/
def pushforwardCompHomUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward f ⋙ pushforward g).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward (f ≫ g)).obj M) :=
  (pushforwardCompForgetIso f g).hom.app M ≫
    (typePushforwardComp f g).hom.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).inv.app M

/-- The reverse underlying type-valued comparison of composite pushforward. -/
def pushforwardCompInvUnderlying {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : X.Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
      ((pushforward (f ≫ g)).obj M) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (structureSheaf Z)).obj
        ((pushforward f ⋙ pushforward g).obj M) :=
  (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom (f ≫ g))).hom.app M ≫
    (typePushforwardComp f g).inv.app
      ((Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj M) ≫
    (pushforwardCompForgetIso f g).inv.app M

/-- The composition of module pushforwards along `f` then `g` identifies with pushforward
along `f ≫ g`. -/
def pushforwardComp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompHomUnderlying f g M) sorry sorry
        inv :=
          Sheaf.InternalModule.homOfUnderlying (structureSheaf Z)
            (pushforwardCompInvUnderlying f g M) sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Successive module pullbacks identify with pullback along the composite morphism, as the
left-adjoint mate of `pushforwardComp`. -/
def pullbackCompIso {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
    (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g)

/-- `pullbackCompIso` is the left-adjoint mate of `pushforwardComp`. -/
theorem pullbackCompIso_eq {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompIso f g =
      Adjunction.leftAdjointCompIso
        (pullbackPushforwardAdjunction g) (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (f ≫ g)) (pushforwardComp f g) :=
  rfl

variable {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The cartesian identification `(f')^* g^* ≅ (g')^* f^*` of module pullbacks. -/
def pullbackCartesianIso (h_cart : IsPullback g' f' f g) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback g' :=
  pullbackCompIso f' g ≪≫
    eqToIso (congrArg pullback h_cart.w.symm) ≪≫
    (pullbackCompIso g' f).symm

/-- The pulled-back cartesian identification is the composite of path-composition
isomorphisms. -/
theorem pullbackCartesianIso_eq (h_cart : IsPullback g' f' f g) :
    pullbackCartesianIso h_cart =
      pullbackCompIso f' g ≪≫
        eqToIso (congrArg pullback h_cart.w.symm) ≪≫
        (pullbackCompIso g' f).symm :=
  rfl

/-- The underived base-change 2-cell `g^* f_* ⟶ f'_* (g')^*` of module functors, as the mate of
the cartesian pullback square. -/
def pushforwardBaseChangeNatTrans (h_cart : IsPullback g' f' f g) :
    pushforward f ⋙ pullback g ⟶ pullback g' ⋙ pushforward f' :=
  CategoryTheory.DerivedBaseChange.map
    (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction f')
    (pullbackCartesianIso h_cart)

/-- The underived comparison is the component of the mate of the cartesian pullback square. -/
theorem pushforwardBaseChangeNatTrans_app (h_cart : IsPullback g' f' f g) (ℱ : X.Modules) :
    (pushforwardBaseChangeNatTrans h_cart).app ℱ =
      CategoryTheory.DerivedBaseChange.app
        (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction f')
        (pullbackCartesianIso h_cart) ℱ :=
  rfl

/-- Exact module pullback commutes with the degree-zero embedding into `D⁺`. -/
def exactPullbackSingleIso {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    DerivedCategory.Plus.singleFunctor Y.Modules 0 ⋙
        ExactFunctor.Derived.Plus.functor (exactPullback φ) ≅
      pullback φ ⋙ DerivedCategory.Plus.singleFunctor X.Modules 0 :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ExactFunctor.Derived.Plus.compιIso (exactPullback φ)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso Y.Modules 0)
        (pullback φ).mapDerivedCategory ≪≫
      (pullback φ).mapDerivedCategorySingleFunctor 0 ≪≫
      Functor.isoWhiskerLeft (pullback φ)
        (DerivedCategory.Plus.singleFunctorιIso X.Modules 0).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- `exactPullbackSingleIso` is the cancellation of the inclusion of `D⁺` into the unbounded
derived category. -/
theorem exactPullbackSingleIso_eq {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    exactPullbackSingleIso φ =
      Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (ExactFunctor.Derived.Plus.compιIso (exactPullback φ)) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso Y.Modules 0)
            (pullback φ).mapDerivedCategory ≪≫
          (pullback φ).mapDerivedCategorySingleFunctor 0 ≪≫
          Functor.isoWhiskerLeft (pullback φ)
            (DerivedCategory.Plus.singleFunctorιIso X.Modules 0).symm ≪≫
          (Functor.associator _ _ _).symm) :=
  rfl

/-- The degree-`i` identification of `R((g')^* f'_*)` with the one-way exact-horizontal target
`(g')^* R f'_*` on algebraic-space modules. -/
def higherDirectImageBaseChangeTargetNatTrans
    [Flat g'] [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] (i : ℕ) :
    (pullback g' ⋙ pushforward f').rightDerived i ⟶
      pullback g' ⋙ (pushforward f').rightDerived i :=
  let Ipull := exactPullback g'
  let Hpush := pushforward f'
  let eTarget :
      Functor.RightDerived.degree
          (ExactFunctor.Derived.Plus.functor Ipull ⋙
            Functor.RightDerived.Bounded.functor Hpush) (i : ℤ) ≅
        Ipull.obj ⋙
          Functor.RightDerived.degree (Functor.RightDerived.Bounded.functor Hpush) (i : ℤ) :=
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor X.Modules 0)
        (Functor.associator (ExactFunctor.Derived.Plus.functor Ipull)
          (Functor.RightDerived.Bounded.functor Hpush)
          (DerivedCategory.Plus.homologyFunctor Y'.Modules (i : ℤ))) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (exactPullbackSingleIso g')
        (Functor.RightDerived.Bounded.functor Hpush ⋙
          DerivedCategory.Plus.homologyFunctor Y'.Modules (i : ℤ)) ≪≫
      Functor.associator _ _ _
  (Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
      (pullback g' ⋙ pushforward f') i).inv ≫
    Functor.RightDerived.degree.map
      (Functor.RightDerived.Composition.BoundedBelow.Square.Exact.targetComparison
        (I := Ipull) (H := Hpush)) (i : ℤ) ≫
    eTarget.hom ≫
    Functor.whiskerLeft (pullback g')
      (Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived Hpush i).hom

/-- Naturality of the one-way exact-horizontal target comparison. -/
theorem higherDirectImageBaseChangeTargetNatTrans_naturality
    [Flat g'] [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (i : ℕ) {ℱ 𝒢 : X.Modules} (α : ℱ ⟶ 𝒢) :
    ((pullback g' ⋙ pushforward f').rightDerived i).map α ≫
        (higherDirectImageBaseChangeTargetNatTrans i).app 𝒢 =
      (higherDirectImageBaseChangeTargetNatTrans i).app ℱ ≫
        (pullback g' ⋙ (pushforward f').rightDerived i).map α :=
  sorry

/-- The canonical base-change 2-cell
`g^* R^i f_* - ⟶ R^i f'_* ((g')^* -)` as a natural transformation of module functors. -/
def higherDirectImageBaseChangeNatTrans (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] (i : ℕ) :
    higherDirectImageFunctor f i ⋙ pullback g ⟶
      pullback g' ⋙ higherDirectImageFunctor f' i :=
  (RightDerived.postcompIso (pushforward f) (pullback g) i).inv ≫
    NatTrans.rightDerived (pushforwardBaseChangeNatTrans h_cart) i ≫
    higherDirectImageBaseChangeTargetNatTrans i

/-- The canonical higher-direct-image base-change morphism
`g^* R^i f_* ℱ ⟶ R^i f'_* ((g')^* ℱ)` of sheaves of modules on `Y'_étale`. -/
def higherDirectImageBaseChangeHom (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    (pullback g).obj (higherDirectImage f ℱ i) ⟶
      higherDirectImage f' ((pullback g').obj ℱ) i :=
  (higherDirectImageBaseChangeNatTrans h_cart i).app ℱ

/-- The module higher-direct-image comparison is the component of the derived base-change
natural transformation. -/
theorem higherDirectImageBaseChangeHom_eq (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    higherDirectImageBaseChangeHom h_cart ℱ i =
      (higherDirectImageBaseChangeNatTrans h_cart i).app ℱ :=
  rfl

/-- Naturality of the objectwise Cohomology-on-Sites 21.15.1 comparison. -/
theorem higherDirectImageBaseChangeHom_naturality (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (i : ℕ) {ℱ 𝒢 : X.Modules} (α : ℱ ⟶ 𝒢) :
    (pullback g).map (higherDirectImageMap f α i) ≫
        higherDirectImageBaseChangeHom h_cart 𝒢 i =
      higherDirectImageBaseChangeHom h_cart ℱ i ≫
        higherDirectImageMap f' ((pullback g').map α) i :=
  sorry

/-- The module higher-direct-image comparison morphism is an isomorphism when `g` is flat,
`f` is quasi-compact and quasi-separated, and `ℱ` is quasi-coherent. -/
instance isIso_higherDirectImageBaseChangeHom (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIso (higherDirectImageBaseChangeHom h_cart ℱ i) :=
  sorry

/-- The identification `g^* R^i f_* ℱ ≅ R^i f'_* ((g')^* ℱ)` of sheaves of modules. -/
def higherDirectImageBaseChangeIso (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    (pullback g).obj (higherDirectImage f ℱ i) ≅
      higherDirectImage f' ((pullback g').obj ℱ) i :=
  asIso (higherDirectImageBaseChangeHom h_cart ℱ i)

/-- The forward map of the module higher-direct-image base-change isomorphism is the comparison
morphism. -/
theorem higherDirectImageBaseChangeIso_hom (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    (higherDirectImageBaseChangeIso h_cart ℱ i).hom =
      higherDirectImageBaseChangeHom h_cart ℱ i :=
  rfl

/-- The small étale object of `ofOver (Spec A)` associated to an open of `Spec A`. -/
def specOpenSmallEtale {A : Type u} [CommRing A]
    (σA : Spec (CommRingCat.of A) ⟶ S) (U : (Over.mk σA).left.Opens) :
    smallEtaleSite (ofOver (Over.mk σA)) :=
  (schemeEtaleToSmallEtale (Over.mk σA)).obj
    ((smallEtaleToOpensRingedHom (Over.mk σA).left).base.obj U)

/-- The morphism of spaces-étale objects over `Spec B` identifying the inverse-image open
with the fibre product of the source open along `Spec.map (algebraMap A B)`. -/
def specOpenPullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    (smallEtaleInclusion (ofOver (Over.mk σB))).obj
        (specOpenSmallEtale σB
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U)) ⟶
      (etaleBaseChange
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj
        (specOpenSmallEtale σA U) :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ U)
  let VA := specOpenSmallEtale σA U
  let iB := smallEtaleInclusion (ofOver (Over.mk σB))
  let iA := smallEtaleInclusion (ofOver (Over.mk σA))
  MorphismProperty.Over.homMk
      (A := iB.obj VB)
      (B := (spacesEtalePullback g).obj (iA.obj VA))
      (pullback.lift
        (ofOverMap (Over.homMk (morphismRestrict s U) sorry) : ofOver VB.left ⟶ ofOver VA.left)
        (iB.obj VB).hom
        sorry)
      sorry ≫
    (smallEtaleInclusion_comp_spacesEtalePullback g).hom.app VA

/-- `specOpenPullbackHom` is an isomorphism of spaces-étale objects. -/
instance isIso_specOpenPullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    IsIso (specOpenPullbackHom σA σB hσ U) :=
  sorry

/-- The reverse spaces-étale comparison of `specOpenPullbackHom`. -/
def specOpenPullbackInv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    (etaleBaseChange
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj
        (specOpenSmallEtale σA U) ⟶
      (smallEtaleInclusion (ofOver (Over.mk σB))).obj
        (specOpenSmallEtale σB
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹ᵁ U)) :=
  inv (specOpenPullbackHom σA σB hσ U)

/-- `specOpenPullbackInv` is the inverse of `specOpenPullbackHom`. -/
theorem specOpenPullbackInv_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (U : (Over.mk σA).left.Opens) :
    specOpenPullbackInv σA σB hσ U = inv (specOpenPullbackHom σA σB hσ U) :=
  rfl

/-- Type-valued component of the `toScheme` direct-image comparison at an open of `Spec A`. -/
def toScheme_pushforwardUnderlyingApp {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) (U : ((Over.mk σA).left.Opens)ᵒᵖ) :
    ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((toScheme (Over.mk σA)).obj
          ((pushforward
              (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N))).obj.obj
      U ⟶
      ((Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          ((toScheme (Over.mk σB)).obj N))).obj.obj U :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := ofOverHomMk s hσ
  let VA := specOpenSmallEtale σA (unop U)
  let VB := specOpenSmallEtale σB (s ⁻¹ᵁ unop U)
  let iB := smallEtaleInclusion (ofOver (Over.mk σB))
  let Nty :=
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf (ofOver (Over.mk σB)))).obj N
  let Nspaces :=
    (iB.sheafPushforwardCocontinuous (Type u)
      (smallEtaleTopology (ofOver (Over.mk σB)))
      (spacesEtaleTopology (ofOver (Over.mk σB)))).obj Nty
  ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)).hom.app N).hom.app
      (op VA) ≫
    Nspaces.obj.map (specOpenPullbackHom σA σB hσ (unop U)).op ≫
    ((iB.op.ranAdjunction (Type u)).counit.app Nty.obj).app (op VB)

/-- Type-valued sheaf morphism of the `toScheme` direct-image comparison. -/
def toScheme_pushforwardUnderlying {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    (Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
      ((toScheme (Over.mk σA)).obj
        ((pushforward
            (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (Over.mk σA).left.ringCatSheaf).obj
        ((Scheme.Modules.pushforward
            (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
          ((toScheme (Over.mk σB)).obj N)) :=
  { hom :=
      { app := fun U ↦ toScheme_pushforwardUnderlyingApp σA σB hσ N U
        naturality := fun _ _ _ ↦ sorry } }

/-- Direct-image comparison of `toScheme` against affine spectrum pushforward. -/
def toScheme_pushforwardHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    (toScheme (Over.mk σA)).obj
        ((pushforward
            (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N) ⟶
      (Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        ((toScheme (Over.mk σB)).obj N) :=
  Sheaf.InternalModule.homOfUnderlying (Over.mk σA).left.ringCatSheaf
    (toScheme_pushforwardUnderlying σA σB hσ N) sorry sorry

/-- `toScheme_pushforwardHom` is an isomorphism on underlying modules. -/
instance isIso_toScheme_pushforwardHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    IsIso (toScheme_pushforwardHom σA σB hσ N) :=
  sorry

/-- Reverse direct-image comparison of `toScheme_pushforwardHom`. -/
def toScheme_pushforwardInv {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    (Scheme.Modules.pushforward
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        ((toScheme (Over.mk σB)).obj N) ⟶
      (toScheme (Over.mk σA)).obj
        ((pushforward
            (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj N) :=
  @CategoryTheory.inv _ _ _ _ (toScheme_pushforwardHom σA σB hσ N)
    (isIso_toScheme_pushforwardHom σA σB hσ N)

/-- `toScheme_pushforwardInv` is the inverse of `toScheme_pushforwardHom`. -/
theorem toScheme_pushforwardInv_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (N : (ofOver (Over.mk σB)).Modules) :
    toScheme_pushforwardInv σA σB hσ N =
      @CategoryTheory.inv _ _ _ _ (toScheme_pushforwardHom σA σB hσ N)
        (isIso_toScheme_pushforwardHom σA σB hσ N) :=
  rfl

/-- Natural transformation of the direct-image `toScheme` square. -/
def toScheme_pushforwardNatTrans {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB) :
    pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ) ⋙
        toScheme (Over.mk σA) ⟶
      toScheme (Over.mk σB) ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  { app := fun N ↦ toScheme_pushforwardHom σA σB hσ N
    naturality := fun _ _ _ ↦ sorry }

/-- Inverse natural transformation of `toScheme_pushforwardNatTrans`. -/
def toScheme_pushforwardInvNatTrans {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB) :
    toScheme (Over.mk σB) ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶
      pushforward (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ) ⋙
        toScheme (Over.mk σA) :=
  { app := fun N ↦ toScheme_pushforwardInv σA σB hσ N
    naturality := fun _ _ _ ↦ sorry }

/-- The comparison `s^* (toScheme G) ⟶ toScheme (g^* G)` of modules on `Spec B`, as the
left-adjoint mate of `toScheme_pushforwardNatTrans`. -/
def toScheme_pullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (G : (ofOver (Over.mk σA)).Modules) :
    (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
      ((toScheme (Over.mk σA)).obj G) ⟶
    (toScheme (Over.mk σB)).obj
      ((pullback (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)).obj G) :=
  ((mateEquiv
        (pullbackPushforwardAdjunction
          (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
        (Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map (CommRingCat.ofHom (algebraMap A B))))).symm
      (toScheme_pushforwardNatTrans σA σB hσ)).app G

/-- `toScheme_pullbackHom` is the component of the mate of `toScheme_pushforwardNatTrans`. -/
theorem toScheme_pullbackHom_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (G : (ofOver (Over.mk σA)).Modules) :
    toScheme_pullbackHom σA σB hσ G =
      ((mateEquiv
            (pullbackPushforwardAdjunction
              (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
            (Scheme.Modules.pullbackPushforwardAdjunction
              (Spec.map (CommRingCat.ofHom (algebraMap A B))))).symm
          (toScheme_pushforwardNatTrans σA σB hσ)).app G :=
  rfl

/-- `toScheme_pullbackHom` is an isomorphism. -/
instance isIso_toScheme_pullbackHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (G : (ofOver (Over.mk σA)).Modules) :
    IsIso (toScheme_pullbackHom σA σB hσ G) :=
  sorry

/-- The left-adjoint square of `toScheme` against affine spectrum pullback. -/
def toScheme_pullbackIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB) :
    toScheme (Over.mk σA) ⋙
        Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      pullback (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ) ⋙
        toScheme (Over.mk σB) :=
  NatIso.ofComponents
    (fun G ↦
      @asIso _ _ _ _ (toScheme_pullbackHom σA σB hσ G)
        (isIso_toScheme_pullbackHom σA σB hσ G))
    sorry

/-- Affine comparison `Γ(Spec A, G) ⊗_A B ⟶ Γ(Spec B, s^* G)` for a module on `Spec A`. -/
def moduleSpec_pullbackExtendScalars {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (G : (Spec (CommRingCat.of A)).Modules) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ⟶
    (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G) :=
  ((tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _)
    ((tilde.ChangeOfRings.Pullback.iso
        (CommRingCat.ofHom (algebraMap A B))).inv.app
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ≫
      (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        ((tilde.adjunction (R := CommRingCat.of A)).counit.app G))

/-- `moduleSpec_pullbackExtendScalars` is the transpose of the tilde-pullback comparison. -/
theorem moduleSpec_pullbackExtendScalars_eq {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (G : (Spec (CommRingCat.of A)).Modules) :
    moduleSpec_pullbackExtendScalars G =
      ((tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _)
        ((tilde.ChangeOfRings.Pullback.iso
            (CommRingCat.ofHom (algebraMap A B))).inv.app
            ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ≫
          (Scheme.Modules.pullback
              (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
            ((tilde.adjunction (R := CommRingCat.of A)).counit.app G)) :=
  rfl

/-- Cohomology `H^i(X, ℱ)` as an `A`-module, realized as global sections of the scheme-module
image of `R^i f_* ℱ` on `Spec A`. -/
def cohomologyOver {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    ModuleCat A :=
  (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
    ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i))

/-- `cohomologyOver` is global sections of `toScheme` of the higher direct image. -/
theorem cohomologyOver_eq {A : Type u} [CommRing A] {X : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (f : X ⟶ ofOver (Over.mk σA))
    [Abelian X.Modules] [Abelian (ofOver (Over.mk σA)).Modules]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) (i : ℕ) :
    cohomologyOver σA f ℱ i =
      (moduleSpecΓFunctor (R := CommRingCat.of A)).obj
        ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)) :=
  rfl

/-- The canonical map `H^i(X, ℱ) ⊗_A B ⟶ H^i(X', (g')^* ℱ)` of `B`-modules. -/
def cohomologyBaseChangeHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj (cohomologyOver σA f ℱ i) ⟶
      cohomologyOver σB f' ((pullback g').obj ℱ) i :=
  moduleSpec_pullbackExtendScalars ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)) ≫
    (moduleSpecΓFunctor (R := CommRingCat.of B)).map
      (toScheme_pullbackHom σA σB hσ (higherDirectImage f ℱ i) ≫
        (toScheme (Over.mk σB)).map (higherDirectImageBaseChangeHom h_cart ℱ i))

/-- `cohomologyBaseChangeHom` is affine global-sections comparison followed by global sections
of `higherDirectImageBaseChangeHom`. -/
theorem cohomologyBaseChangeHom_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i =
      moduleSpec_pullbackExtendScalars ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)) ≫
        (moduleSpecΓFunctor (R := CommRingCat.of B)).map
          (toScheme_pullbackHom σA σB hσ (higherDirectImage f ℱ i) ≫
            (toScheme (Over.mk σB)).map (higherDirectImageBaseChangeHom h_cart ℱ i)) :=
  rfl

/-- The affine cohomology comparison is an isomorphism under flat base change. -/
instance isIso_cohomologyBaseChangeHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIso (cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i) :=
  sorry

/-- The identification `H^i(X, ℱ) ⊗_A B ≅ H^i(X', (g')^* ℱ)` of affine cohomology modules. -/
def cohomologyBaseChangeIso {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj (cohomologyOver σA f ℱ i) ≅
      cohomologyOver σB f' ((pullback g').obj ℱ) i :=
  asIso (cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i)

/-- The forward map of the affine cohomology base-change isomorphism is the comparison
morphism. -/
theorem cohomologyBaseChangeIso_hom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    (cohomologyBaseChangeIso σA σB hσ g' f' f h_cart ℱ i).hom =
      cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i :=
  rfl

/-- Forgetful form of the affine identification, after the named comparison map. -/
theorem cohomology_baseChange_of_flat {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      ((ModuleCat.extendScalars (algebraMap A B)).obj (cohomologyOver σA f ℱ i))
      (cohomologyOver σB f' ((pullback g').obj ℱ) i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
