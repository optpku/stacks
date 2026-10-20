/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Lifts

/-!
# Presheaf of isomorphism classes of infinitesimal lifts

For a fibre object `x` over `Spec A` and an `S`-algebra map `A' ⟶ A`, an
affine test object `U` over `Spec A'` determines the thickening
`U ×_{Spec A'} Spec A`. The associated presheaf on `(Spec A').AffineOver`
sends `U` to isomorphism classes of lifts of the restriction of `x` along
this thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The infinitesimal thickening `U ×_{Spec A'} Spec A` of an affine scheme
`U` over `Spec A'` along `A' ⟶ A`. -/
def infinitesimalLiftThickening {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) : Scheme.{u} :=
  pullback (Scheme.AffineOver.obj U).hom (Spec.map fA)

/-- `infinitesimalLiftThickening fA U` is the scheme pullback of the structure
morphism of `U` along `Spec.map fA`. -/
theorem infinitesimalLiftThickening_eq {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) :
    infinitesimalLiftThickening fA U =
      pullback (Scheme.AffineOver.obj U).hom (Spec.map fA) :=
  rfl

/-- The first projection of the infinitesimal thickening, to the affine test
object `U`. -/
def infinitesimalLiftThickeningFst {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) :
    infinitesimalLiftThickening fA U ⟶ (Scheme.AffineOver.toScheme (Spec A')).obj U :=
  pullback.fst (Scheme.AffineOver.obj U).hom (Spec.map fA)

/-- The first projection of the thickening is the pullback projection to `U`. -/
theorem infinitesimalLiftThickeningFst_eq {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) :
    infinitesimalLiftThickeningFst fA U =
      pullback.fst (Scheme.AffineOver.obj U).hom (Spec.map fA) :=
  rfl

/-- The second projection of the infinitesimal thickening, to `Spec A`. -/
def infinitesimalLiftThickeningSnd {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) :
    infinitesimalLiftThickening fA U ⟶ Spec A :=
  pullback.snd (Scheme.AffineOver.obj U).hom (Spec.map fA)

/-- The second projection of the thickening is the pullback projection to
`Spec A`. -/
theorem infinitesimalLiftThickeningSnd_eq {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    (U : (Spec A').AffineOver) :
    infinitesimalLiftThickeningSnd fA U =
      pullback.snd (Scheme.AffineOver.obj U).hom (Spec.map fA) :=
  rfl

/-- The structure morphism of the infinitesimal thickening over `S`. -/
def infinitesimalLiftThickeningToS {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) (U : (Spec A').AffineOver) :
    infinitesimalLiftThickening fA U ⟶ S :=
  infinitesimalLiftThickeningSnd fA U ≫ σA

/-- The structure morphism of the thickening is the composite of the second
projection with `σA`. -/
theorem infinitesimalLiftThickeningToS_eq {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) (U : (Spec A').AffineOver) :
    infinitesimalLiftThickeningToS σA fA U = infinitesimalLiftThickeningSnd fA U ≫ σA :=
  rfl

/-- Compatibility of the thickening projections with the structure morphisms
over `S`. -/
theorem infinitesimalLiftThickeningOverHom_w {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) (U : (Spec A').AffineOver) :
    infinitesimalLiftThickeningFst fA U ≫ (Scheme.AffineOver.obj U).hom ≫ σA' =
      infinitesimalLiftThickeningSnd fA U ≫ σA :=
  sorry

/-- The thickening arrow in `Over S`, from `U ×_{Spec A'} Spec A` to `U`. -/
def infinitesimalLiftThickeningOverHom {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) (U : (Spec A').AffineOver) :
    Over.mk (infinitesimalLiftThickeningToS σA fA U) ⟶
      Over.mk ((Scheme.AffineOver.obj U).hom ≫ σA') :=
  Over.homMk (infinitesimalLiftThickeningFst fA U)
    (infinitesimalLiftThickeningOverHom_w σA σA' fA hfA U)

/-- The left component of the thickening arrow is the first pullback
projection. -/
theorem infinitesimalLiftThickeningOverHom_left {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) (U : (Spec A').AffineOver) :
    (infinitesimalLiftThickeningOverHom σA σA' fA hfA U).left =
      infinitesimalLiftThickeningFst fA U :=
  rfl

/-- The `Over S` arrow along which `x` is restricted to the thickening. -/
def infinitesimalLiftRestrictOverHom {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) (U : (Spec A').AffineOver) :
    Over.mk (infinitesimalLiftThickeningToS σA fA U) ⟶ Over.mk σA :=
  Over.homMk (infinitesimalLiftThickeningSnd fA U) rfl

/-- The left component of the restriction base arrow is the second pullback
projection. -/
theorem infinitesimalLiftRestrictOverHom_left {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) (U : (Spec A').AffineOver) :
    (infinitesimalLiftRestrictOverHom σA fA U).left = infinitesimalLiftThickeningSnd fA U :=
  rfl

/-- The restriction `y = x|_{U ×_{Spec A'} Spec A}` of a fibre object along the
thickening. -/
def infinitesimalLiftRestrict {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (fA : A' ⟶ A)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :
    X.p.Fiber (Over.mk (infinitesimalLiftThickeningToS σA fA U)) :=
  Chosen.reindexObj X.p (infinitesimalLiftRestrictOverHom σA fA U) x

/-- Restriction of `x` to the thickening is reindexing along the second
projection. -/
theorem infinitesimalLiftRestrict_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (fA : A' ⟶ A)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :
    infinitesimalLiftRestrict σA fA x U =
      Chosen.reindexObj X.p (infinitesimalLiftRestrictOverHom σA fA U) x :=
  rfl

/-- The category of objects over an affine test scheme `U` lifting the
restriction of `x` to the infinitesimal thickening `U ×_{Spec A'} Spec A`. -/
abbrev infinitesimalLiftCat {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :=
  UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
    (infinitesimalLiftRestrict σA fA x U)

/-- `infinitesimalLiftCat fA hfA x U` is the fibered lift category of the
restricted fibre object along the infinitesimal thickening of `U`. -/
theorem infinitesimalLiftCat_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :
    infinitesimalLiftCat fA hfA x U =
      UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
        (infinitesimalLiftRestrict σA fA x U) :=
  rfl

/-- Compatibility of an affine morphism over `Spec A'` with the structure
morphisms to `S`. -/
theorem infinitesimalLiftAffineOverHom_w {S : Scheme.{u}} {A' : CommRingCat.{u}}
    (σA' : Spec A' ⟶ S) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    (Scheme.AffineOver.hom f).left ≫ (Scheme.AffineOver.obj U).hom ≫ σA' =
      (Scheme.AffineOver.obj V).hom ≫ σA' :=
  sorry

/-- An affine morphism over `Spec A'`, viewed as a morphism in `Over S`. -/
def infinitesimalLiftAffineOverHom {S : Scheme.{u}} {A' : CommRingCat.{u}}
    (σA' : Spec A' ⟶ S) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    Over.mk ((Scheme.AffineOver.obj V).hom ≫ σA') ⟶
      Over.mk ((Scheme.AffineOver.obj U).hom ≫ σA') :=
  Over.homMk (Scheme.AffineOver.hom f).left (infinitesimalLiftAffineOverHom_w σA' f)

/-- The left component of the induced `Over S` arrow is the underlying scheme
morphism of `f`. -/
theorem infinitesimalLiftAffineOverHom_left {S : Scheme.{u}} {A' : CommRingCat.{u}}
    (σA' : Spec A' ⟶ S) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    (infinitesimalLiftAffineOverHom σA' f).left = (Scheme.AffineOver.hom f).left :=
  rfl

/-- The first projection of a morphism of affine test objects, as a commuting
square of structure morphisms over `Spec A'`. -/
theorem infinitesimalLiftThickeningMap_fst {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    (Scheme.AffineOver.obj V).hom ≫ 𝟙 (Spec A') =
      (Scheme.AffineOver.hom f).left ≫ (Scheme.AffineOver.obj U).hom :=
  sorry

/-- The second projection of a morphism of affine test objects is the identity
on `Spec A`. -/
theorem infinitesimalLiftThickeningMap_snd {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    Spec.map fA ≫ 𝟙 (Spec A') = 𝟙 (Spec A) ≫ Spec.map fA :=
  sorry

/-- The induced map of thickenings along a morphism of affine test objects. -/
def infinitesimalLiftThickeningMap {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftThickening fA V ⟶ infinitesimalLiftThickening fA U :=
  pullback.map (Scheme.AffineOver.obj V).hom (Spec.map fA)
    (Scheme.AffineOver.obj U).hom (Spec.map fA)
    (Scheme.AffineOver.hom f).left (𝟙 (Spec A)) (𝟙 (Spec A'))
    (infinitesimalLiftThickeningMap_fst fA f)
    (infinitesimalLiftThickeningMap_snd fA f)

/-- The induced map of thickenings is the canonical map of pullbacks. -/
theorem infinitesimalLiftThickeningMap_eq {A A' : CommRingCat.{u}} (fA : A' ⟶ A)
    {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftThickeningMap fA f =
      pullback.map (Scheme.AffineOver.obj V).hom (Spec.map fA)
        (Scheme.AffineOver.obj U).hom (Spec.map fA)
        (Scheme.AffineOver.hom f).left (𝟙 (Spec A)) (𝟙 (Spec A'))
        (infinitesimalLiftThickeningMap_fst fA f)
        (infinitesimalLiftThickeningMap_snd fA f) :=
  rfl

/-- Compatibility of the induced thickening map with the structure morphisms
over `S`. -/
theorem infinitesimalLiftThickeningOverHomMap_w {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftThickeningMap fA f ≫ infinitesimalLiftThickeningToS σA fA U =
      infinitesimalLiftThickeningToS σA fA V :=
  sorry

/-- The induced map of thickenings, as a morphism in `Over S`. -/
def infinitesimalLiftThickeningOverHomMap {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    Over.mk (infinitesimalLiftThickeningToS σA fA V) ⟶
      Over.mk (infinitesimalLiftThickeningToS σA fA U) :=
  Over.homMk (infinitesimalLiftThickeningMap fA f)
    (infinitesimalLiftThickeningOverHomMap_w σA fA f)

/-- The left component of the induced thickening arrow is the map of
pullbacks. -/
theorem infinitesimalLiftThickeningOverHomMap_left {S : Scheme.{u}}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (fA : A' ⟶ A)
    {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    (infinitesimalLiftThickeningOverHomMap σA fA f).left =
      infinitesimalLiftThickeningMap fA f :=
  rfl

/-- The square of thickening arrows associated to a morphism of affine test
objects commutes in `Over S`. -/
theorem infinitesimalLiftThickeningCommSq {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S) (fA : A' ⟶ A)
    (hfA : Spec.map fA ≫ σA' = σA) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    CommSq (infinitesimalLiftThickeningOverHom σA σA' fA hfA V)
      (infinitesimalLiftThickeningOverHomMap σA fA f)
      (infinitesimalLiftAffineOverHom σA' f)
      (infinitesimalLiftThickeningOverHom σA σA' fA hfA U) :=
  sorry

/-- Restricting `x` along the composite thickening projection equals
restricting first to `U` and then along the induced map of thickenings. -/
theorem infinitesimalLiftRestrictOverHom_comp {S : Scheme.{u}} {A A' : CommRingCat.{u}}
    (σA : Spec A ⟶ S) (fA : A' ⟶ A) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftThickeningOverHomMap σA fA f ≫
        infinitesimalLiftRestrictOverHom σA fA U =
      infinitesimalLiftRestrictOverHom σA fA V :=
  sorry

/-- The comparison from the iterated restriction of a fibre object to its
direct restriction along a morphism of thickenings. -/
def infinitesimalLiftRestrictConnect {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (fA : A' ⟶ A)
    (x : X.p.Fiber (Over.mk σA)) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    Chosen.reindexObj X.p (infinitesimalLiftThickeningOverHomMap σA fA f)
        ((fiberFunctor (𝟙 X) (Over.mk (infinitesimalLiftThickeningToS σA fA U))).obj
          (infinitesimalLiftRestrict σA fA x U)) ⟶
      infinitesimalLiftRestrict σA fA x V :=
  eqToHom
      (congrArg
        (fun F ↦
          Chosen.reindexObj X.p (infinitesimalLiftThickeningOverHomMap σA fA f)
            (F.obj (infinitesimalLiftRestrict σA fA x U)))
        (fiberFunctor.id X (Over.mk (infinitesimalLiftThickeningToS σA fA U)))) ≫
    (Chosen.Reindex.specifiedCompIsoApp X.p
        (infinitesimalLiftRestrictOverHom σA fA U)
        (infinitesimalLiftThickeningOverHomMap σA fA f)
        (infinitesimalLiftRestrictOverHom σA fA V)
        (infinitesimalLiftRestrictOverHom_comp σA fA f) x).inv

/-- The connecting morphism is the identity-cleavage transport of the specified
reindexing comparison along the thickening square. -/
theorem infinitesimalLiftRestrictConnect_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (fA : A' ⟶ A)
    (x : X.p.Fiber (Over.mk σA)) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftRestrictConnect σA fA x f =
      eqToHom
          (congrArg
            (fun F ↦
              Chosen.reindexObj X.p (infinitesimalLiftThickeningOverHomMap σA fA f)
                (F.obj (infinitesimalLiftRestrict σA fA x U)))
            (fiberFunctor.id X (Over.mk (infinitesimalLiftThickeningToS σA fA U)))) ≫
        (Chosen.Reindex.specifiedCompIsoApp X.p
            (infinitesimalLiftRestrictOverHom σA fA U)
            (infinitesimalLiftThickeningOverHomMap σA fA f)
            (infinitesimalLiftRestrictOverHom σA fA V)
            (infinitesimalLiftRestrictOverHom_comp σA fA f) x).inv :=
  rfl

/-- The functor of lift categories along a morphism of affine test objects,
induced by `CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor (𝟙 X)` on the thickening square. -/
def infinitesimalLiftRestrictFunctor {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S)
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
        (infinitesimalLiftRestrict σA fA x U) ⥤
      UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA V)
        (infinitesimalLiftRestrict σA fA x V) :=
  CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor (𝟙 X)
    (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
    (infinitesimalLiftThickeningOverHom σA σA' fA hfA V)
    (infinitesimalLiftThickeningOverHomMap σA fA f)
    (infinitesimalLiftAffineOverHom σA' f)
    (infinitesimalLiftThickeningCommSq σA σA' fA hfA f)
    (infinitesimalLiftRestrictConnect σA fA x f)

/-- Restriction of lift categories is `CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor (𝟙 X)` on the thickening
square. -/
theorem infinitesimalLiftRestrictFunctor_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} (σA : Spec A ⟶ S) (σA' : Spec A' ⟶ S)
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    infinitesimalLiftRestrictFunctor σA σA' fA hfA x f =
      CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor (𝟙 X)
        (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
        (infinitesimalLiftThickeningOverHom σA σA' fA hfA V)
        (infinitesimalLiftThickeningOverHomMap σA fA f)
        (infinitesimalLiftAffineOverHom σA' f)
        (infinitesimalLiftThickeningCommSq σA σA' fA hfA f)
        (infinitesimalLiftRestrictConnect σA fA x f) :=
  rfl

/-- Restriction along an identity affine-site arrow induces the identity on
isomorphism classes of infinitesimal lifts. -/
theorem infinitesimalLiftPresheaf_map_id {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOverᵒᵖ) :
    isomorphismClasses.map
        (infinitesimalLiftRestrictFunctor σA σA' fA hfA x (𝟙 U).unop).toCatHom =
      𝟙 (isomorphismClasses.obj
        (Cat.of (UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U.unop)
          (infinitesimalLiftRestrict σA fA x U.unop)))) :=
  sorry

/-- Restriction along a composite of opposite affine-site arrows induces the
composite maps on isomorphism classes of infinitesimal lifts. -/
theorem infinitesimalLiftPresheaf_map_comp {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) {U V W : (Spec A').AffineOverᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    isomorphismClasses.map
        (infinitesimalLiftRestrictFunctor σA σA' fA hfA x (f ≫ g).unop).toCatHom =
      isomorphismClasses.map
          (infinitesimalLiftRestrictFunctor σA σA' fA hfA x f.unop).toCatHom ≫
        isomorphismClasses.map
          (infinitesimalLiftRestrictFunctor σA σA' fA hfA x g.unop).toCatHom :=
  sorry

/-- The presheaf on `(Aff / Spec A')` sending an affine test object to the
isomorphism classes of infinitesimal lifts of `x` along the corresponding
thickening. -/
def infinitesimalLiftPresheaf {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) :
    (Spec A').AffineOverᵒᵖ ⥤ Type (u + 1) where
  obj U :=
    isomorphismClasses.obj
      (Cat.of (UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U.unop)
        (infinitesimalLiftRestrict σA fA x U.unop)))
  map {U V} f :=
    isomorphismClasses.map
      (infinitesimalLiftRestrictFunctor σA σA' fA hfA x f.unop).toCatHom
  map_id := infinitesimalLiftPresheaf_map_id fA hfA x
  map_comp := infinitesimalLiftPresheaf_map_comp fA hfA x

/-- The value of the infinitesimal-lift presheaf at an affine test object is
the type of isomorphism classes of lifts of the restricted fibre object. -/
theorem infinitesimalLiftPresheaf_obj {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) (U : (Spec A').AffineOver) :
    (infinitesimalLiftPresheaf fA hfA x).obj (op U) =
      isomorphismClasses.obj
        (Cat.of (UnderLift X.p (infinitesimalLiftThickeningOverHom σA σA' fA hfA U)
          (infinitesimalLiftRestrict σA fA x U))) :=
  rfl

/-- Restriction maps of the infinitesimal-lift presheaf are the maps of
isomorphism classes induced by `CategoryTheory.FiberedCategoryOver.Groupoids.liftFunctor (𝟙 X)` on the thickening square. -/
theorem infinitesimalLiftPresheaf_map {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)) {U V : (Spec A').AffineOver} (f : V ⟶ U) :
    (infinitesimalLiftPresheaf fA hfA x).map f.op =
      isomorphismClasses.map
        (infinitesimalLiftRestrictFunctor σA σA' fA hfA x f).toCatHom :=
  rfl

end AlgebraicGeometry.GroupoidsOver
