/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback

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

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange

/-! # Higher direct image base-change comparisons -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for definitional equality of higher direct images.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Module pullback along a flat morphism of algebraic spaces is additive. -/
instance pullback_additive {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (pullback φ).Additive :=
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

/-- Module pullback along a flat morphism of algebraic spaces preserves homology. -/
instance pullback_preservesHomology {X Y : AlgebraicSpace S} (φ : X ⟶ Y) [Flat φ]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (pullback φ).PreservesHomology :=
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
    NatTrans.rightDerived (Modules.baseChange h_cart.w) i ≫
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

/-- Naturality of the higher-direct-image base-change comparison. -/
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

end AlgebraicGeometry.AlgebraicSpace.Modules
