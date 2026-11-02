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

set_option backward.isDefEq.respectTransparency false

/-- The base projection commutes with restriction to test schemes. -/
private theorem baseMap_naturality {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Z X : Over B) {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (presheaf Z.hom X.hom).map f ≫
        TypeCat.ofHom (fun (p : Pair Z.hom X.hom V.unop) ↦ ULift.up (yonedaEquiv p.a)) =
      TypeCat.ofHom (fun (p : Pair Z.hom X.hom U.unop) ↦ ULift.up (yonedaEquiv p.a)) ≫
        (toSheaf.obj B).obj.map f := by
  ext p
  change yonedaEquiv (yoneda.map f.unop ≫ p.a) =
    B.functorOfPoints.map f (yonedaEquiv p.a)
  exact (yonedaEquiv_naturality' p.a f).symm

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

private theorem spacePair_map_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T T' T'' : AlgebraicSpace S} (p : SpacePair Z X T)
    (f : T'' ⟶ T') (g : T' ⟶ T) :
    SpacePair.map (f ≫ g) p = SpacePair.map f (SpacePair.map g p) := by
  dsimp only [SpacePair.map, SpacePair.fiberMap]
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.homMk_left, pullback.lift_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [Over.homMk_left, pullback.lift_snd]
    simp only [← Category.assoc, pullback.map_comp, Category.id_comp]
    exact (pullback.lift_snd _ _ _).symm

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
        (presheaf Z.hom X.hom).map f := by
  ext x
  change SpacePair.schemeEquiv Z X V.unop
      (SpacePair.map (yonedaEquiv.symm (T.functorOfPoints.map f x.down)) p) =
    (SpacePair.schemeEquiv Z X U.unop
      (SpacePair.map (yonedaEquiv.symm x.down) p)).restrict f.unop
  rw [yonedaEquiv_symm_map]
  exact congrArg (SpacePair.schemeEquiv Z X V.unop)
    (spacePair_map_comp (T' := ofOver U.unop) (T'' := ofOver V.unop) p
      (yoneda.map f.unop : ofOver V.unop ⟶ ofOver U.unop)
      (yonedaEquiv.symm x.down : ofOver U.unop ⟶ T))

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

private theorem toPair_a_app {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (t : T.functorOfPoints.obj U) :
    (toPair_a v).app U t = yonedaEquiv (toPairEval v t).a := rfl

private theorem toPairEval_map {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom)
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) (t : T.functorOfPoints.obj U) :
    toPairEval v (T.functorOfPoints.map f t) = (toPairEval v t).restrict f.unop := by
  exact congrArg (fun k : ULift.{u + 1} (T.functorOfPoints.obj U) ⟶
    Pair Z.hom X.hom V.unop ↦ k (ULift.up t)) (v.hom.naturality f)

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
  by
    rw [Category.id_comp]
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    change (toPair_a v).app U (toPairFst v x) = Z.hom.app U (toPairSnd v x)
    exact congrArg (fun k : pullback (toPair_a v) Z.hom ⟶ B ↦ k.app U x)
      (pullback.condition (f := toPair_a v) (g := Z.hom))

/-- The canonical section `U ⟶ U ×_{a_U, B} Z` of a `U`-point of `T ×_{a, B} Z`. -/
private def toPairSection {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    ofOver U.unop ⟶ pullback (toPairEval v (toPairFst v x)).a Z.hom :=
  pullback.lift (𝟙 _)
    (yonedaEquiv.symm (toPairSnd v x) : ofOver U.unop ⟶ Z.left)
    (toPairSection_overB v x)

private theorem toPairSection_fst {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    toPairSection v x ≫ pullback.fst (toPairEval v (toPairFst v x)).a Z.hom =
      𝟙 (ofOver U.unop) := pullback.lift_fst _ _ _

private theorem toPairSection_snd {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U : (Over S)ᵒᵖ}
    (x : (pullback (toPair_a v) Z.hom).functorOfPoints.obj U) :
    toPairSection v x ≫ pullback.snd (toPairEval v (toPairFst v x)).a Z.hom =
      yonedaEquiv.symm (toPairSnd v x) := pullback.lift_snd _ _ _

private theorem pair_restrict_toMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {U V W : Over S} (f : V ⟶ U)
    (p : Pair Z.hom X.hom U) (q : Pair Z.hom X.hom V) (hq : q = p.restrict f)
    (s : ofOver W ⟶ pullback p.a Z.hom) (t : ofOver W ⟶ pullback q.a Z.hom)
    (hf : (t ≫ pullback.fst q.a Z.hom) ≫ (yoneda.map f : ofOver V ⟶ ofOver U) =
      s ≫ pullback.fst p.a Z.hom)
    (hz : t ≫ pullback.snd q.a Z.hom = s ≫ pullback.snd p.a Z.hom) :
    t ≫ BaseChangeMorphism.toMap q.b = s ≫ BaseChangeMorphism.toMap p.b := by
  subst q
  dsimp only [Pair.restrict, mk] at hf hz
  dsimp only [Pair.restrict, mk]
  rw [BaseChangeMorphism.toMap_ofMap, ← Category.assoc]
  exact congrArg (fun k : ofOver W ⟶ pullback p.a Z.hom ↦
    k ≫ BaseChangeMorphism.toMap p.b) (pullback.hom_ext
      (by simpa only [Category.assoc, pullback.lift_fst] using hf)
      (by simpa only [Category.assoc, pullback.lift_snd, Category.comp_id] using hz))

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
  by
    have hfst : toPairFst v
        ((pullback (toPair_a v) Z.hom).functorOfPoints.map f x) =
        T.functorOfPoints.map f (toPairFst v x) :=
      ConcreteCategory.congr_hom ((pullback.fst (toPair_a v) Z.hom).naturality f) x
    have hsnd : toPairSnd v
        ((pullback (toPair_a v) Z.hom).functorOfPoints.map f x) =
        Z.left.functorOfPoints.map f (toPairSnd v x) :=
      ConcreteCategory.congr_hom ((pullback.snd (toPair_a v) Z.hom).naturality f) x
    rw [yonedaEquiv_naturality']
    apply congrArg (yonedaEquiv (X := V.unop) (F := X.left.functorOfPoints))
    apply pair_restrict_toMap f.unop _ _
      (by rw [hfst]; exact toPairEval_map v f (toPairFst v x))
      ((yoneda.map f.unop : ofOver V.unop ⟶ ofOver U.unop) ≫ toPairSection v x)
      (toPairSection v ((pullback (toPair_a v) Z.hom).functorOfPoints.map f x))
    · erw [toPairSection_fst, Category.id_comp, Category.assoc,
        toPairSection_fst, Category.comp_id]
    · erw [toPairSection_snd, Category.assoc, toPairSection_snd]
      rw [hsnd, yonedaEquiv_symm_map]
      rfl

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
  by
    apply NatTrans.ext
    funext U
    ext x
    change yonedaEquiv ((toPairSection v x ≫
        BaseChangeMorphism.toMap (toPairEval v (toPairFst v x)).b) ≫ X.hom) =
      yonedaEquiv (toPairEval v (toPairFst v x)).a
    erw [Category.assoc, BaseChangeMorphism.toMap_comm (toPairEval v (toPairFst v x)).b,
      ← Category.assoc]
    erw [toPairSection_fst, Category.id_comp]

/-- The relative-morphism pair over `T` associated to a sheaf morphism `T ⟶ Mor_B(Z, X)`. -/
def toPair {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    SpacePair Z X T :=
  SpacePair.ofOverMorph (toPair_a v) (toPair_b v) (toPair_b_over_base v)

private theorem toPair_toOverMorph {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    SpacePair.toOverMorph (toPair v) = toPair_b v := pullback.lift_snd _ _ _

private theorem spacePair_ext {S : Scheme.{u}} {B : AlgebraicSpace S} {Z X : Over B}
    {T : AlgebraicSpace S} {p q : SpacePair Z X T} (ha : p.base = q.base)
    (hb : ∀ (U : Over S) (r : ofOver U ⟶ pullback p.base Z.hom)
      (s : ofOver U ⟶ pullback q.base Z.hom),
      r ≫ pullback.fst p.base Z.hom = s ≫ pullback.fst q.base Z.hom →
      r ≫ pullback.snd p.base Z.hom = s ≫ pullback.snd q.base Z.hom →
      r ≫ SpacePair.toOverMorph p = s ≫ SpacePair.toOverMorph q) : p = q := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  dsimp only at ha
  subst a'
  have hm : (b.left ≫ pullback.snd a X.hom : pullback a Z.hom ⟶ X.left) =
      b'.left ≫ pullback.snd a X.hom := by
    apply hom_ext_yoneda (P := (pullback a Z.hom).functorOfPoints)
      (Q := X.left.functorOfPoints)
    intro U r
    exact hb U r r rfl rfl
  have hh : b = b' := by
    apply Over.OverMorphism.ext
    exact pullback.hom_ext ((Over.w b).trans (Over.w b').symm) hm
  exact congrArg (SpacePair.mk a) hh

private theorem spacePair_map_toOverMorph {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T T' : AlgebraicSpace S} (h : T' ⟶ T) (p : SpacePair Z X T) :
    SpacePair.toOverMorph (SpacePair.map h p) =
      SpacePair.fiberMap h p ≫ SpacePair.toOverMorph p := pullback.lift_snd _ _ _

private theorem schemeEquiv_symm_toOverMorph {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {U : Over S} (p : Pair Z.hom X.hom U) :
    SpacePair.toOverMorph ((SpacePair.schemeEquiv Z X U).symm p) =
      BaseChangeMorphism.toMap p.b := rfl

private theorem spacePair_map_compare {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T T' : AlgebraicSpace S} (h : T' ⟶ T)
    (p : SpacePair Z X T) (q : SpacePair Z X T') (hq : q = SpacePair.map h p)
    {U : Over S} (s : ofOver U ⟶ pullback p.base Z.hom)
    (t : ofOver U ⟶ pullback q.base Z.hom)
    (hf : (t ≫ pullback.fst q.base Z.hom) ≫ h = s ≫ pullback.fst p.base Z.hom)
    (hz : t ≫ pullback.snd q.base Z.hom = s ≫ pullback.snd p.base Z.hom) :
    t ≫ SpacePair.toOverMorph q = s ≫ SpacePair.toOverMorph p := by
  subst q
  dsimp only [SpacePair.map] at hf hz
  have hc : t ≫ SpacePair.fiberMap h p = s := by
    apply pullback.hom_ext
    · simpa only [SpacePair.fiberMap, Category.assoc, pullback.lift_fst] using hf
    · simpa only [SpacePair.fiberMap, Category.assoc, pullback.lift_snd,
        Category.comp_id] using hz
  erw [spacePair_map_toOverMorph, ← Category.assoc, hc]

private theorem toPair_b_on_restriction {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S}
    (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) {U V : Over S}
    (t : T.functorOfPoints.obj (op U)) (f : V ⟶ U)
    (r : ofOver V ⟶ pullback (toPair_a v) Z.hom)
    (s : ofOver V ⟶ pullback (toPairEval v t).a Z.hom)
    (hr : r ≫ pullback.fst (toPair_a v) Z.hom =
      (yoneda.map f : ofOver V ⟶ ofOver U) ≫ yonedaEquiv.symm t)
    (hs : s ≫ pullback.fst (toPairEval v t).a Z.hom =
      (yoneda.map f : ofOver V ⟶ ofOver U))
    (hz : r ≫ pullback.snd (toPair_a v) Z.hom =
      s ≫ pullback.snd (toPairEval v t).a Z.hom) :
    r ≫ toPair_b v = s ≫ BaseChangeMorphism.toMap (toPairEval v t).b := by
  apply yonedaEquiv.injective
  change yonedaEquiv (toPairSection v (yonedaEquiv r) ≫
      BaseChangeMorphism.toMap (toPairEval v (toPairFst v (yonedaEquiv r))).b) =
    yonedaEquiv (s ≫ BaseChangeMorphism.toMap (toPairEval v t).b)
  apply congrArg (yonedaEquiv (X := V) (F := X.left.functorOfPoints))
  have heval : toPairEval v (toPairFst v (yonedaEquiv r)) = (toPairEval v t).restrict f := by
    change toPairEval v (yonedaEquiv (r ≫ pullback.fst (toPair_a v) Z.hom)) = _
    erw [hr]
    erw [← yonedaEquiv_naturality (yonedaEquiv.symm t) f, Equiv.apply_symm_apply]
    exact toPairEval_map v f.op t
  apply pair_restrict_toMap f _ _ heval s (toPairSection v (yonedaEquiv r))
  · erw [toPairSection_fst, Category.id_comp]
    exact hs.symm
  · erw [toPairSection_snd]
    change yonedaEquiv.symm (yonedaEquiv (r ≫ pullback.snd (toPair_a v) Z.hom)) = _
    rw [Equiv.symm_apply_apply]
    exact hz

/-- Reconstructing a pair and then restricting it recovers the sheaf morphism. -/
private theorem toSheafHom_toPair {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S} (v : toSheaf.obj T ⟶ sheaf Z.hom X.hom) :
    SpacePair.toSheafHom (toPair v) = v := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext t
  apply (SpacePair.schemeEquiv Z X U.unop).symm.injective
  change SpacePair.map (yonedaEquiv.symm t.down : ofOver U.unop ⟶ T) (toPair v) =
    (SpacePair.schemeEquiv Z X U.unop).symm (toPairEval v t.down)
  apply spacePair_ext
  · apply yonedaEquiv.injective
    change yonedaEquiv ((yonedaEquiv.symm t.down : ofOver U.unop ⟶ T) ≫ toPair_a v) =
      yonedaEquiv (toPairEval v t.down).a
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact toPair_a_app v t.down
  · intro V r s hf hz
    let f : V ⟶ U.unop := yonedaEquiv (s ≫ pullback.fst (toPairEval v t.down).a Z.hom)
    have hs : s ≫ pullback.fst (toPairEval v t.down).a Z.hom =
        (yoneda.map f : ofOver V ⟶ ofOver U.unop) := by
      apply yonedaEquiv.injective
      exact (yonedaEquiv_yoneda_map f).symm
    erw [spacePair_map_toOverMorph, schemeEquiv_symm_toOverMorph,
      toPair_toOverMorph, ← Category.assoc]
    apply toPair_b_on_restriction v t.down f _ s
    · dsimp only [SpacePair.fiberMap]
      erw [Category.assoc, pullback.lift_fst, ← Category.assoc]
      exact congrArg (fun k : ofOver V ⟶ ofOver U.unop ↦
        k ≫ (yonedaEquiv.symm t.down : ofOver U.unop ⟶ T)) (hf.trans hs)
    · exact hs
    · dsimp only [SpacePair.fiberMap]
      erw [Category.assoc, pullback.lift_snd, Category.comp_id]
      exact hz

/-- Restricting a pair and then reconstructing it recovers the pair. -/
private theorem toPair_toSheafHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {Z X : Over B} {T : AlgebraicSpace S} (p : SpacePair Z X T) :
    toPair (SpacePair.toSheafHom p) = p := by
  let v := SpacePair.toSheafHom p
  apply spacePair_ext
  · apply NatTrans.ext
    funext U
    ext t
    change yonedaEquiv ((SpacePair.map (T' := ofOver U.unop)
        (yonedaEquiv.symm t : ofOver U.unop ⟶ T) p).base) =
      p.base.app U t
    change yonedaEquiv ((yonedaEquiv.symm t : ofOver U.unop ⟶ T) ≫ p.base) = _
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  · intro U r s hf hz
    change r ≫ SpacePair.toOverMorph (toPair v) = s ≫ SpacePair.toOverMorph p
    erw [toPair_toOverMorph]
    apply yonedaEquiv.injective
    change yonedaEquiv (toPairSection v (yonedaEquiv r) ≫
        BaseChangeMorphism.toMap (toPairEval v (toPairFst v (yonedaEquiv r))).b) =
      yonedaEquiv (s ≫ SpacePair.toOverMorph p)
    apply congrArg (yonedaEquiv (X := U) (F := X.left.functorOfPoints))
    have heval :
        (SpacePair.schemeEquiv Z X U).symm (toPairEval v (toPairFst v (yonedaEquiv r))) =
        SpacePair.map (r ≫ pullback.fst (toPair_a v) Z.hom) p := by
      apply (SpacePair.schemeEquiv Z X U).injective
      change (SpacePair.toSheafHom p).hom.app (op U)
          (ULift.up (yonedaEquiv (r ≫ pullback.fst (toPair_a v) Z.hom))) = _
      rw [SpacePair.toSheafHom_app, Equiv.symm_apply_apply]
      rfl
    apply spacePair_map_compare (T' := ofOver U)
      (r ≫ pullback.fst (toPair_a v) Z.hom) p
      ((SpacePair.schemeEquiv Z X U).symm (toPairEval v (toPairFst v (yonedaEquiv r))))
      heval s (toPairSection v (yonedaEquiv r))
    · erw [toPairSection_fst, Category.id_comp]
      exact hf
    · erw [toPairSection_snd]
      change yonedaEquiv.symm (yonedaEquiv (r ≫ pullback.snd (toPair_a v) Z.hom)) = _
      rw [Equiv.symm_apply_apply]
      exact hz

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
