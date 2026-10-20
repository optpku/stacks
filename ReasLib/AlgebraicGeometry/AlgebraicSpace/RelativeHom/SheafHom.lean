/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.SpacePair

/-!
# The relative-Hom fppf sheaf

The functor `Mor_B(Z, X)` is an fppf sheaf on `Sch/S`, and morphisms of sheaves
out of an algebraic space `T` correspond to relative-morphism pairs over `T`.
-/

public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- The base projection commutes with restriction to test schemes. -/
private theorem baseMap_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (presheaf Z.hom X.hom).map f ≫
        TypeCat.ofHom (fun (p : Pair Z.hom X.hom V.unop) ↦ ULift.up (yonedaEquiv p.a)) =
      TypeCat.ofHom (fun (p : Pair Z.hom X.hom U.unop) ↦ ULift.up (yonedaEquiv p.a)) ≫
        (toSheaf.obj B).obj.map f := sorry

/-- The underlying presheaf morphism of `baseMap`, sending a pair `(a, b)` to the
universe-lift of the Yoneda equivalent of `a`. -/
private def baseMap_hom {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    (sheaf Z.hom X.hom).obj ⟶ (toSheaf.obj B).obj where
  app T := TypeCat.ofHom fun p ↦ ULift.up (yonedaEquiv p.a)
  naturality := fun _ _ f ↦ baseMap_naturality Z X f

/-- The structure morphism `Mor_B(Z, X) ⟶ B` of fppf sheaves. -/
def baseMap {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B) :
    sheaf Z.hom X.hom ⟶ toSheaf.obj B :=
  Sheaf.homEquiv.symm (baseMap_hom Z X)

/-- The component of `baseMap` at `T` sends a pair to the universe-lift of the
Yoneda equivalent of its base morphism. -/
theorem baseMap_app {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : (Over S)ᵒᵖ) (p : Pair Z.hom X.hom T.unop) :
    (baseMap Z X).hom.app T p = ULift.up (yonedaEquiv p.a) := by rfl

/-- Restricting an algebraic-space pair commutes with scheme restriction. -/
private theorem toSheafHom_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S} (p : SpacePair Z X T)
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (toSheaf.obj T).obj.map f ≫
        TypeCat.ofHom (fun (x : ULift.{u + 1} (T.functorOfPoints.obj V)) ↦
          SpacePair.schemeEquiv Z X V.unop
            (SpacePair.map (yonedaEquiv.symm x.down : ofOver V.unop ⟶ T) p)) =
      TypeCat.ofHom (fun (x : ULift.{u + 1} (T.functorOfPoints.obj U)) ↦
          SpacePair.schemeEquiv Z X U.unop
            (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p)) ≫
        (presheaf Z.hom X.hom).map f := sorry

/-- The presheaf morphism associated to a pair over an algebraic space, sending a
scheme-valued point of `T` to the restricted pair. -/
private def ofPair_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    (toSheaf.obj T).obj ⟶ (sheaf Z.hom X.hom).obj where
  app U := TypeCat.ofHom fun x ↦
    SpacePair.schemeEquiv Z X U.unop
      (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p)
  naturality := fun _ _ f ↦ toSheafHom_naturality p f

/-- The sheaf morphism `T ⟶ Mor_B(Z, X)` associated to a pair `(a, b)` over `T`. -/
def SpacePair.toSheafHom {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    toSheaf.obj T ⟶ sheaf Z.hom X.hom :=
  Sheaf.homEquiv.symm (ofPair_hom p)

/-- Components of `SpacePair.toSheafHom` restrict the algebraic-space pair along the underlying
`T`-point. -/
theorem SpacePair.toSheafHom_app {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (p : SpacePair Z X T) (U : (Over S)ᵒᵖ)
    (x : ULift.{u + 1} (T.functorOfPoints.obj U)) :
    (SpacePair.toSheafHom p).hom.app U x =
      SpacePair.schemeEquiv Z X U.unop
        (SpacePair.map (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T) p) := by rfl

/-- The morphism `a : T ⟶ B` recovered from a sheaf map `T ⟶ Mor_B(Z, X)` by the
structure morphism `Mor_B(Z, X) ⟶ B` and full faithfulness of universe lifting. -/
private def toPair_a {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) : T ⟶ B :=
  (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight (Over S)ᵒᵖ).preimage
    (v ≫ baseMap Z X).hom

/-- The scheme-level pair obtained by evaluating a sheaf map on a `T`-point. -/
private def toPairEval {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (t : T.functorOfPoints.obj U) : Pair Z.hom X.hom U.unop :=
  (v.hom.app U) (ULift.up t)

/-- The `T`-point of a `U`-point of `T ×_{a, B} Z`. -/
private def toPairFst {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    T.functorOfPoints.obj U :=
  (pullback.fst (toPair_a v) Z.hom).app U x

/-- The `Z`-point of a `U`-point of `T ×_{a, B} Z`. -/
private def toPairSnd {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    Z.left.functorOfPoints.obj U :=
  (pullback.snd (toPair_a v) Z.hom).app U x

/-- The canonical section of `U ×_{a_U, B} Z` over a `U`-point of `T ×_{a, B} Z`
lies over `B`. -/
private theorem toPairSection_overB {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    𝟙 (ofOver U.unop) ≫ (toPairEval v (toPairFst v x)).a =
      (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z.left) ≫ Z.hom :=
  sorry

/-- The canonical section `U ⟶ U ×_{a_U, B} Z` of a `U`-point of `T ×_{a, B} Z`. -/
private def toPairSection {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    ofOver U.unop ⟶ pullback (toPairEval v (toPairFst v x)).a Z.hom :=
  pullback.lift (𝟙 _)
    (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z.left)
    (toPairSection_overB v x)

/-- The pointwise recovered morphism commutes with scheme restriction. -/
private theorem toPair_b_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S}
    (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U V : (Over S)ᵒᵖ} (f : U ⟶ V)
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    yonedaEquiv (toPairSection v ((pullback (toPair_a v) Z.hom).functorOfPoints.map f x) ≫
      BaseChangeMorphism.toMap (toPairEval v (toPairFst v
        ((pullback (toPair_a v) Z.hom).functorOfPoints.map f x))).b) =
      X.left.functorOfPoints.map f (yonedaEquiv
        (toPairSection v x ≫ BaseChangeMorphism.toMap (toPairEval v (toPairFst v x)).b)) :=
  sorry

/-- The morphism `T ×_{a, B} Z ⟶ X` recovered from a sheaf map
`T ⟶ Mor_B(Z, X)`. -/
private def toPair_b {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    pullback (toPair_a v) Z.hom ⟶ X.left where
  app U := TypeCat.ofHom fun x ↦
    yonedaEquiv
      (toPairSection v x ≫ BaseChangeMorphism.toMap (toPairEval v (toPairFst v x)).b)
  naturality := by
    intro U V f
    ext x
    exact toPair_b_naturality v f x

/-- The morphism `toPair_b v` makes the triangle over `B` commute. -/
private theorem toPair_b_over_base {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    toPair_b v ≫ X.hom = pullback.fst (toPair_a v) Z.hom ≫ toPair_a v :=
  sorry

/-- The relative-morphism pair over `T` associated to a sheaf morphism `T ⟶ Mor_B(Z, X)`. -/
def toPair {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    SpacePair Z X T :=
  SpacePair.ofOverMorph (toPair_a v) (toPair_b v) (toPair_b_over_base v)

/-- Reconstructing a pair and then restricting it recovers the sheaf morphism. -/
private theorem toSheafHom_toPair {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    SpacePair.toSheafHom (toPair v) = v := sorry

/-- Restricting a pair and then reconstructing it recovers the pair. -/
private theorem toPair_toSheafHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    toPair (SpacePair.toSheafHom p) = p := sorry

/-- Sheaf morphisms `T ⟶ Mor_B(Z, X)` correspond to relative-morphism pairs over the algebraic
space `T`. -/
def homEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    (T : AlgebraicSpace S) :
    (toSheaf.obj T ⟶ sheaf Z.hom X.hom) ≃ SpacePair Z X T where
  toFun := toPair
  invFun := SpacePair.toSheafHom
  left_inv := by exact toSheafHom_toPair
  right_inv := by exact toPair_toSheafHom

/-- `homEquiv` sends a sheaf morphism to the associated pair. -/
theorem homEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    homEquiv Z X T v = toPair v := by rfl

/-- The inverse of `homEquiv` sends a pair to the associated sheaf morphism. -/
theorem homEquiv_symm_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (Z X : Over B)
    {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    (homEquiv Z X T).symm p = SpacePair.toSheafHom p := by rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
