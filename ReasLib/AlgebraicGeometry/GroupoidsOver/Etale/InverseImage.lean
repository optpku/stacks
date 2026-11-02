/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafComparison

/-!
# Inverse-image identification of small-étale restrictions

A 1-morphism `f : Y ⟶ X` of categories fibred in groupoids identifies the
small-étale restriction of `f⁻¹ F` at `y` with the small-étale restriction of
`F` at `f(y)`, after reindexing along `p(f(y)) = p(y)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Scheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {Y X : GroupoidsOver S} (f : Y ⟶ X)

/-- Scheme identification `p(f(y)) = p(y)` induced by commutativity of `f`. -/
theorem map_obj_left_eq (y : Y.total) :
    (X.p.obj ((toFunctor f).obj y)).left = (Y.p.obj y).left :=
  congrArg Over.left (Functor.congr_obj (comm f) y)

/-- The functor on small étale sites induced by `p(f(y)) = p(y)`. -/
def transportEtaleFunctor (y : Y.total) :
    (Y.p.obj y).left.Etale ⥤ (X.p.obj ((toFunctor f).obj y)).left.Etale :=
  (eqToIso (congrArg (fun U : Scheme.{u} => Cat.of U.Etale)
      (map_obj_left_eq f y).symm)).hom.toFunctor

/-- Transport of an étale neighborhood of `p(y)` to an étale neighborhood of
`p(f(y))` along `map_obj_left_eq`. -/
def transportEtale (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (X.p.obj ((toFunctor f).obj y)).left.Etale :=
  (transportEtaleFunctor f y).obj V'

/-- Transport of morphisms of étale neighborhoods along `map_obj_left_eq`. -/
def transportEtale_map (y : Y.total) {V' W' : (Y.p.obj y).left.Etale} (i : V' ⟶ W') :
    transportEtale f y V' ⟶ transportEtale f y W' :=
  (transportEtaleFunctor f y).map i

/-- The object map of `transportEtaleFunctor` is `transportEtale`. -/
theorem transportEtaleFunctor_obj (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (transportEtaleFunctor f y).obj V' = transportEtale f y V' :=
  rfl

/-- The cartesian lift of `x` along `V'` projects to `etaleOver x V'`. -/
private theorem smallEtaleEval_toBase_domain_eq {Z : GroupoidsOver S} (x : Z.total)
    (V' : (Z.p.obj x).left.Etale) :
    Z.p.obj ((smallEtaleEval x).obj V') = (etaleOver x V').left :=
  by
    letI := Chosen.cartesianHom.isStronglyCartesian Z.p (etaleOver x V').hom ⟨x, rfl⟩
    exact IsHomLift.domain_eq Z.p (etaleOver x V').hom (smallEtaleEval_toBase x V')

/-- Transporting an étale neighborhood along equality of objects of `Over S`
identifies its domain and its structural morphism. -/
private theorem etaleOver_transport_eq (A B : Over S) (h : A = B)
    (V' : B.left.Etale) :
    let T := (eqToIso (congrArg (fun U : Scheme.{u} => Cat.of U.Etale)
      (congrArg Over.left h).symm)).hom.toFunctor
    let a := (Over.iteratedSliceBackward A).obj ((Scheme.Etale.forget A.left).obj (T.obj V'))
    let b := (Over.iteratedSliceBackward B).obj ((Scheme.Etale.forget B.left).obj V')
    ∃ e : b.left = a.left, b.hom ≫ eqToHom h.symm = eqToHom e ≫ a.hom := by
  cases h
  exact ⟨rfl, by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp⟩

/-- Domain identification for the cartesian fill-in of `smallEtaleEval_map_app`. -/
private theorem smallEtaleEval_map_domain_eq (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.obj ((toFunctor f).obj ((smallEtaleEval y).obj V')) =
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).left :=
  by
    obtain ⟨h, _⟩ := etaleOver_transport_eq
      (X.p.obj ((toFunctor f).obj y)) (Y.p.obj y) (Functor.congr_obj (comm f) y) V'
    exact ((Functor.congr_obj (comm f) ((smallEtaleEval y).obj V')).trans
      (smallEtaleEval_toBase_domain_eq y V')).trans h

/-- Base morphism in `Over S` underlying `f` applied to the étale lift of `y`. -/
private def smallEtaleEval_map_base (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V') ⟶
      X.p.obj ((toFunctor f).obj y) :=
  X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V'))

/-- The image of `smallEtaleEval_toBase y V'` under `f` and the cartesian lift of
`f(y)` lie over composable morphisms of `Over S`. -/
private theorem smallEtaleEval_map_app_comp (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_base f y V' =
      eqToHom (smallEtaleEval_map_domain_eq f y V') ≫
        (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom :=
  by
    obtain ⟨_, h⟩ := etaleOver_transport_eq
      (X.p.obj ((toFunctor f).obj y)) (Y.p.obj y) (Functor.congr_obj (comm f) y) V'
    change X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')) = _
    rw [show X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')) =
      eqToHom (Functor.congr_obj (comm f) ((smallEtaleEval y).obj V')) ≫
        Y.p.map (smallEtaleEval_toBase y V') ≫
          eqToHom (Functor.congr_obj (comm f) y).symm from
      Functor.congr_hom (comm f) (smallEtaleEval_toBase y V')]
    dsimp only [smallEtaleEval_toBase]
    rw [Chosen.cartesianHom.map]
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    erw [h]
    simp only [eqToHom_trans_assoc]
    rfl

/-- The reverse triangle identity for the inverse cartesian fill-in. -/
private theorem smallEtaleEval_map_app_inv_comp (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    X.p.map (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V')) =
      eqToHom
        ((smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y) (transportEtale f y V')).trans
          (smallEtaleEval_map_domain_eq f y V').symm) ≫
        smallEtaleEval_map_base f y V' :=
  by
    rw [smallEtaleEval_map_app_comp]
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id] using
      (Chosen.cartesianHom.map X.p
        (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
        ⟨(toFunctor f).obj y, rfl⟩)

/-- Cartesian fill-in comparing `f` applied to the étale lift of `y` with the
étale lift of `f(y)`, obtained from the universal property of
`smallEtaleEval_toBase (f(y))`. -/
def smallEtaleEval_map_app (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval y ⋙ toFunctor f).obj V' ⟶
      (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
    (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V'))
    (Chosen.cartesianHom.isStronglyCartesian X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
      ⟨(toFunctor f).obj y, rfl⟩) _ _
    (eqToHom (by exact smallEtaleEval_map_domain_eq f y V') :
      X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V') ⟶
        (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).left)
    (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
    (by exact smallEtaleEval_map_app_comp f y V')
    ((toFunctor f).map (smallEtaleEval_toBase y V'))
    (IsHomLift.map X.p ((toFunctor f).map (smallEtaleEval_toBase y V')))

/-- Inverse cartesian fill-in of `smallEtaleEval_map_app`, obtained from the
universal property of the strongly cartesian image of
`smallEtaleEval_toBase y`. -/
def smallEtaleEval_map_app_inv (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') ⟶
      (smallEtaleEval y ⋙ toFunctor f).obj V' :=
  @IsStronglyCartesian.map _ _ _ _ X.p _ _ _ _
    (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
    ((toFunctor f).map (smallEtaleEval_toBase y V'))
    (IsFibered.isStronglyCartesian_of_isCartesian X.p
      (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
      ((toFunctor f).map (smallEtaleEval_toBase y V'))) _ _
    (eqToHom (by
        exact (smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y)
          (transportEtale f y V')).trans (smallEtaleEval_map_domain_eq f y V').symm) :
      X.p.obj ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V')) ⟶
        X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V'))
    (X.p.map (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V')))
    (by exact smallEtaleEval_map_app_inv_comp f y V')
    (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V'))
    inferInstance

/-- Triangle identity for `smallEtaleEval_map_app` against the cartesian lift of
`f(y)`. -/
theorem smallEtaleEval_map_app_triangle (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app f y V' ≫
        smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V') =
      (toFunctor f).map (smallEtaleEval_toBase y V') :=
  by
    letI := Chosen.cartesianHom.isStronglyCartesian X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
      ⟨(toFunctor f).obj y, rfl⟩
    unfold smallEtaleEval_map_app
    apply IsStronglyCartesian.fac

/-- Triangle identity for `smallEtaleEval_map_app_inv` against the image of the
cartesian lift of `y`. -/
theorem smallEtaleEval_map_app_inv_triangle (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app_inv f y V' ≫
        (toFunctor f).map (smallEtaleEval_toBase y V') =
      smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V') :=
  by
    letI := IsFibered.isStronglyCartesian_of_isCartesian X.p
      (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
      ((toFunctor f).map (smallEtaleEval_toBase y V'))
    unfold smallEtaleEval_map_app_inv
    apply IsStronglyCartesian.fac

/-- Both cartesian comparison arrows lie over the identity of the étale domain. -/
private theorem smallEtaleEval_map_app_lifts (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    let U := (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).left
    X.p.IsHomLift (𝟙 U) (smallEtaleEval_map_app f y V') ∧
      X.p.IsHomLift (𝟙 U) (smallEtaleEval_map_app_inv f y V') := by
  dsimp only
  let h := smallEtaleEval_map_domain_eq f y V'
  let k := smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y) (transportEtale f y V')
  have hf : X.p.IsHomLift (eqToHom h) (smallEtaleEval_map_app f y V') := by
    unfold smallEtaleEval_map_app
    apply IsStronglyCartesian.map_isHomLift
  have hi : X.p.IsHomLift (eqToHom (k.trans h.symm))
      (smallEtaleEval_map_app_inv f y V') := by
    unfold smallEtaleEval_map_app_inv
    apply IsStronglyCartesian.map_isHomLift
  constructor
  · exact (IsHomLift.lift_eqToHom_comp_iff X.p (𝟙 _)
      (smallEtaleEval_map_app f y V') h).mp (by simpa only [Category.comp_id] using hf)
  · haveI := hi
    have hi' := IsHomLift.lift_comp_eqToHom X.p (eqToHom (k.trans h.symm))
      (smallEtaleEval_map_app_inv f y V') h
    have hi'' : X.p.IsHomLift (eqToHom k) (smallEtaleEval_map_app_inv f y V') := by
      simpa only [eqToHom_trans] using hi'
    exact (IsHomLift.lift_eqToHom_comp_iff X.p (𝟙 _)
      (smallEtaleEval_map_app_inv f y V') k).mp
        (by simpa only [Category.comp_id] using hi'')

/-- The forward cartesian comparison followed by the reverse comparison is the identity. -/
private theorem smallEtaleEval_map_app_hom_inv_id (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app f y V' ≫ smallEtaleEval_map_app_inv f y V' = 𝟙 _ :=
  by
    obtain ⟨hf, hi⟩ := smallEtaleEval_map_app_lifts f y V'
    haveI hf' : X.p.IsHomLift
        (𝟙 (X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V')))
        (smallEtaleEval_map_app f y V') := by
      exact Eq.mpr (congrArg
        (fun U : Over S => X.p.IsHomLift (𝟙 U) (smallEtaleEval_map_app f y V'))
        (smallEtaleEval_map_domain_eq f y V')) hf
    haveI hi' : X.p.IsHomLift
        (𝟙 (X.p.obj ((smallEtaleEval y ⋙ toFunctor f).obj V')))
        (smallEtaleEval_map_app_inv f y V') := by
      exact Eq.mpr (congrArg
        (fun U : Over S => X.p.IsHomLift (𝟙 U) (smallEtaleEval_map_app_inv f y V'))
        (smallEtaleEval_map_domain_eq f y V')) hi
    haveI hcomp : X.p.IsHomLift
        (𝟙 (X.p.obj ((toFunctor f).obj ((smallEtaleEval y).obj V'))))
        (smallEtaleEval_map_app f y V' ≫ smallEtaleEval_map_app_inv f y V') :=
      @IsHomLift.comp_of_lift_id _ _ _ _ X.p _ _ _ _ _ _ hf' hi'
    haveI hid : X.p.IsHomLift
        (𝟙 (X.p.obj ((toFunctor f).obj ((smallEtaleEval y).obj V'))))
        (𝟙 ((smallEtaleEval y ⋙ toFunctor f).obj V')) :=
      IsHomLift.id (p := X.p) rfl
    letI := IsFibered.isStronglyCartesian_of_isCartesian X.p
      (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
      ((toFunctor f).map (smallEtaleEval_toBase y V'))
    apply IsStronglyCartesian.ext X.p
      (X.p.map ((toFunctor f).map (smallEtaleEval_toBase y V')))
      ((toFunctor f).map (smallEtaleEval_toBase y V')) (𝟙 _)
    simp only [Category.assoc, smallEtaleEval_map_app_inv_triangle,
      smallEtaleEval_map_app_triangle, Category.id_comp]

/-- The reverse cartesian comparison followed by the forward comparison is the identity. -/
private theorem smallEtaleEval_map_app_inv_hom_id (y : Y.total)
    (V' : (Y.p.obj y).left.Etale) :
    smallEtaleEval_map_app_inv f y V' ≫ smallEtaleEval_map_app f y V' = 𝟙 _ :=
  by
    obtain ⟨hf, hi⟩ := smallEtaleEval_map_app_lifts f y V'
    letI := hf
    letI := hi
    haveI := IsHomLift.id (p := X.p)
      (smallEtaleEval_toBase_domain_eq ((toFunctor f).obj y) (transportEtale f y V'))
    letI := Chosen.cartesianHom.isStronglyCartesian X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
      ⟨(toFunctor f).obj y, rfl⟩
    apply IsStronglyCartesian.ext X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y V')).hom
      (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y V')) (𝟙 _)
    simp only [Category.assoc, smallEtaleEval_map_app_triangle,
      smallEtaleEval_map_app_inv_triangle, Category.id_comp]

/-- `smallEtaleEval_map_app` is an isomorphism of objects of the total category. -/
def smallEtaleEval_map_appIso (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval y ⋙ toFunctor f).obj V' ≅
      (smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V') where
  hom := smallEtaleEval_map_app f y V'
  inv := smallEtaleEval_map_app_inv f y V'
  hom_inv_id := by exact smallEtaleEval_map_app_hom_inv_id f y V'
  inv_hom_id := by exact smallEtaleEval_map_app_inv_hom_id f y V'

/-- An evaluation map lies over the corresponding morphism of étale neighborhoods. -/
private theorem smallEtaleEval_map_lift {Z : GroupoidsOver S} (x : Z.total)
    {V' W' : (Z.p.obj x).left.Etale} (i : V' ⟶ W') :
    Z.p.IsHomLift
      (((Over.iteratedSliceBackward (Z.p.obj x)).map
        ((Scheme.Etale.forget (Z.p.obj x).left).map i)).left)
      ((smallEtaleEval x).map i) := by
  let χ := Cleavage.ofIsFibered Z.p
  let j := (Over.iteratedSliceBackward (Z.p.obj x)).map
    ((Scheme.Etale.forget (Z.p.obj x).left).map i)
  exact @IsStronglyCartesian.map_isHomLift _ _ _ _ Z.p _ _ _ _
    (etaleOver x W').hom (χ.cartesianHom (etaleOver x W').hom ⟨x, rfl⟩)
    (χ.reindexLift (etaleOver x W').hom ⟨x, rfl⟩).isStronglyCartesian _ _
    j.left (etaleOver x V').hom (Over.w j).symm
    (χ.cartesianHom (etaleOver x V').hom ⟨x, rfl⟩)
    (χ.reindexLift (etaleOver x V').hom ⟨x, rfl⟩).isStronglyCartesian.toIsHomLift

/-- Evaluation maps commute with the chosen arrows to the original object. -/
private theorem smallEtaleEval_map_toBase {Z : GroupoidsOver S} (x : Z.total)
    {V' W' : (Z.p.obj x).left.Etale} (i : V' ⟶ W') :
    (smallEtaleEval x).map i ≫ smallEtaleEval_toBase x W' = smallEtaleEval_toBase x V' := by
  let χ := Cleavage.ofIsFibered Z.p
  let j := (Over.iteratedSliceBackward (Z.p.obj x)).map
    ((Scheme.Etale.forget (Z.p.obj x).left).map i)
  exact @IsStronglyCartesian.fac _ _ _ _ Z.p _ _ _ _
    (etaleOver x W').hom (χ.cartesianHom (etaleOver x W').hom ⟨x, rfl⟩)
    (χ.reindexLift (etaleOver x W').hom ⟨x, rfl⟩).isStronglyCartesian _ _
    j.left (etaleOver x V').hom (Over.w j).symm
    (χ.cartesianHom (etaleOver x V').hom ⟨x, rfl⟩)
    (χ.reindexLift (etaleOver x V').hom ⟨x, rfl⟩).isStronglyCartesian.toIsHomLift

/-- Reindexing an étale morphism along an equality commutes with its map in `Over S`. -/
private theorem etaleOver_transport_map_eq (A B : Over S) (h : A = B)
    {V' W' : B.left.Etale} (i : V' ⟶ W') :
    let T := (eqToIso (congrArg (fun U : Scheme.{u} => Cat.of U.Etale)
      (congrArg Over.left h).symm)).hom.toFunctor
    let a := T ⋙ Scheme.Etale.forget A.left ⋙ Over.iteratedSliceBackward A
    let b := Scheme.Etale.forget B.left ⋙ Over.iteratedSliceBackward B
    ∀ (hV : (b.obj V').left = (a.obj V').left)
      (hW : (b.obj W').left = (a.obj W').left),
      (b.map i).left ≫ eqToHom hW = eqToHom hV ≫ (a.map i).left := by
  cases h
  dsimp only
  intro hV hW
  change ((Over.iteratedSliceBackward A).map ((Scheme.Etale.forget A.left).map i)).left ≫ 𝟙 _ =
    𝟙 _ ≫ ((Over.iteratedSliceBackward A).map ((Scheme.Etale.forget A.left).map i)).left
  simp

/-- Naturality of `smallEtaleEval_map_app` in the étale neighborhood. -/
theorem smallEtaleEval_map_naturality (y : Y.total)
    {V' W' : (Y.p.obj y).left.Etale} (i : V' ⟶ W') :
    (smallEtaleEval y ⋙ toFunctor f).map i ≫ smallEtaleEval_map_app f y W' =
      smallEtaleEval_map_app f y V' ≫
        (smallEtaleEval ((toFunctor f).obj y)).map (transportEtale_map f y i) :=
  by
    obtain ⟨hV, _⟩ := etaleOver_transport_eq
      (X.p.obj ((toFunctor f).obj y)) (Y.p.obj y) (Functor.congr_obj (comm f) y) V'
    obtain ⟨hW, _⟩ := etaleOver_transport_eq
      (X.p.obj ((toFunctor f).obj y)) (Y.p.obj y) (Functor.congr_obj (comm f) y) W'
    let j := (Over.iteratedSliceBackward (Y.p.obj y)).map
      ((Scheme.Etale.forget (Y.p.obj y).left).map i)
    let k := (Over.iteratedSliceBackward (X.p.obj ((toFunctor f).obj y))).map
      ((Scheme.Etale.forget (X.p.obj ((toFunctor f).obj y)).left).map (transportEtale_map f y i))
    have hbase : j.left ≫ eqToHom hW = eqToHom hV ≫ k.left :=
      etaleOver_transport_map_eq _ _ (Functor.congr_obj (comm f) y) i hV hW
    haveI hy : Y.p.IsHomLift j.left ((smallEtaleEval y).map i) :=
      smallEtaleEval_map_lift y i
    haveI hx : X.p.IsHomLift k.left
        ((smallEtaleEval ((toFunctor f).obj y)).map (transportEtale_map f y i)) :=
      smallEtaleEval_map_lift ((toFunctor f).obj y) (transportEtale_map f y i)
    haveI hfy : X.p.IsHomLift j.left ((toFunctor f).map ((smallEtaleEval y).map i)) :=
      BasedFunctor.preserves_isHomLift (toBasedFunctor f) j.left ((smallEtaleEval y).map i)
    haveI hfy' : X.p.IsHomLift (j.left ≫ eqToHom hW)
        ((toFunctor f).map ((smallEtaleEval y).map i)) :=
      IsHomLift.lift_comp_eqToHom X.p j.left _ hW
    haveI hφW := (smallEtaleEval_map_app_lifts f y W').1
    haveI hφV := (smallEtaleEval_map_app_lifts f y V').1
    haveI hφV' : X.p.IsHomLift (eqToHom hV) (smallEtaleEval_map_app f y V') := by
      simpa only [Category.comp_id] using
        (@IsHomLift.lift_eqToHom_comp _ _ _ _ X.p _ _ _ _
          (𝟙 _) (smallEtaleEval_map_app f y V') hφV _ hV)
    haveI hl : X.p.IsHomLift (j.left ≫ eqToHom hW)
        ((smallEtaleEval y ⋙ toFunctor f).map i ≫ smallEtaleEval_map_app f y W') :=
      @IsHomLift.comp_lift_id_right _ _ _ _ X.p _ _ _ _ _
        (j.left ≫ eqToHom hW) _ hfy' _ hφW
    haveI hr : X.p.IsHomLift (j.left ≫ eqToHom hW)
        (smallEtaleEval_map_app f y V' ≫
          (smallEtaleEval ((toFunctor f).obj y)).map (transportEtale_map f y i)) := by
      rw [hbase]
      exact IsHomLift.comp X.p _ _ _ _
    letI := Chosen.cartesianHom.isStronglyCartesian X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y W')).hom
      ⟨(toFunctor f).obj y, rfl⟩
    apply IsStronglyCartesian.ext X.p
      (etaleOver ((toFunctor f).obj y) (transportEtale f y W')).hom
      (smallEtaleEval_toBase ((toFunctor f).obj y) (transportEtale f y W'))
      (j.left ≫ eqToHom hW)
    simp only [Functor.comp_map, Category.assoc, smallEtaleEval_map_app_triangle,
      smallEtaleEval_map_toBase, ← Functor.map_comp]

/-- Natural isomorphism identifying étale evaluation of `y` after `f` with étale
evaluation of `f(y)`. -/
def smallEtaleEval_map (y : Y.total) :
    smallEtaleEval y ⋙ toFunctor f ≅
      transportEtaleFunctor f y ⋙ smallEtaleEval ((toFunctor f).obj y) :=
  NatIso.ofComponents (fun V' ↦ smallEtaleEval_map_appIso f y V')
    (fun i ↦ smallEtaleEval_map_naturality f y i)

/-- The component of `smallEtaleEval_map` is `smallEtaleEval_map_app`. -/
theorem smallEtaleEval_map_hom_app (y : Y.total) (V' : (Y.p.obj y).left.Etale) :
    (smallEtaleEval_map f y).hom.app V' = smallEtaleEval_map_app f y V' :=
  rfl

variable [HasSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify Y.etaleTopology (Type (u + 1))]
variable [HasWeakSheafify X.etaleTopology (Type (u + 1))]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]

/-- Restriction of `F` at `f(y)`, reindexed to the small étale site of `p(y)`. -/
def restrictSmallEtaleSheaf_reindex (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    Sheaf (Y.p.obj y).left.smallEtaleTopology (Type (u + 1)) where
  obj :=
    (transportEtaleFunctor f y).op ⋙ (restrictSmallEtaleSheaf F ((toFunctor f).obj y)).obj
  property := by
    have htransport (U V : Scheme.{u}) (h : U = V)
        (G : Sheaf U.smallEtaleTopology (Type (u + 1))) :
        Presheaf.IsSheaf V.smallEtaleTopology
          ((eqToIso (congrArg (fun W : Scheme.{u} => Cat.of W.Etale) h.symm)).hom.toFunctor.op ⋙
            G.obj) := by
      cases h
      change Presheaf.IsSheaf U.smallEtaleTopology G.obj
      exact G.property
    exact htransport _ _ (map_obj_left_eq f y) (restrictSmallEtaleSheaf F ((toFunctor f).obj y))

/-- The underlying presheaf of `restrictSmallEtaleSheaf_reindex` is reindexing of
`restrictSmallEtaleSheaf F (f(y))` along `transportEtaleFunctor`. -/
theorem restrictSmallEtaleSheaf_reindex_obj (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (restrictSmallEtaleSheaf_reindex f y F).obj =
      (transportEtaleFunctor f y).op ⋙
        (restrictSmallEtaleSheaf F ((toFunctor f).obj y)).obj :=
  rfl

/-- Component isomorphism of the inverse-image restriction identification over an
étale neighborhood `V'`. -/
def restrictSmallEtaleSheaf_inverseImage_app (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) ≅
      F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) :=
  (((Functor.isoWhiskerRight
      (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
        (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S))
      (sheafToPresheaf Y.etaleTopology (Type (u + 1)))).app F).app
        (op ((smallEtaleEval y).obj V')) ≪≫
    (toCartesianBasedFunctor f).toFunctor.sheafPushforwardContinuousObjObjIso (Type (u + 1))
      (J := Y.etaleTopology) (K := X.etaleTopology) F ((smallEtaleEval y).obj V')) ≪≫
    F.obj.mapIso (smallEtaleEval_map_appIso f y V').symm.op

/-- The forward component of the canonical inverse-image restriction identification. -/
def restrictSmallEtaleSheaf_inverseImage_app_hom (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) ⟶
      F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) :=
  (restrictSmallEtaleSheaf_inverseImage_app f y F V').hom

/-- The inverse component of the canonical inverse-image restriction identification. -/
def restrictSmallEtaleSheaf_inverseImage_app_inv (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    F.obj.obj
        (op ((smallEtaleEval ((toFunctor f).obj y)).obj (transportEtale f y V'))) ⟶
      ((((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F).obj.obj
        (op ((smallEtaleEval y).obj V'))) :=
  (restrictSmallEtaleSheaf_inverseImage_app f y F V').inv

/-- Underlying presheaf isomorphism of the inverse-image restriction
identification. -/
def restrictSmallEtaleSheaf_inverseImage_presheaf (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (restrictSmallEtaleSheaf
        (((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F)
        y).obj ≅
      (restrictSmallEtaleSheaf_reindex f y F).obj :=
  NatIso.ofComponents
    (fun V' ↦ restrictSmallEtaleSheaf_inverseImage_app f y F (unop V'))
    (fun i ↦ by
      letI : (toFunctor f).IsContinuous Y.etaleTopology X.etaleTopology :=
        CartesianBasedFunctor.inheritedTopology.isContinuous
          (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S)
      let α := ((Functor.isoWhiskerRight
        (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
          (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S))
        (sheafToPresheaf Y.etaleTopology (Type (u + 1)))).app F) ≪≫
          ((toFunctor f).sheafPushforwardContinuousCompSheafToPresheafIso
            (Type (u + 1)) Y.etaleTopology X.etaleTopology).app F
      let β := Functor.isoWhiskerLeft (smallEtaleEval y).op α ≪≫
        Functor.isoWhiskerRight (NatIso.op (smallEtaleEval_map f y).symm) F.obj
      exact β.hom.naturality i)

/-- Canonical identification `f⁻¹ F|_{U_étale} = F|_{U_étale}` of small étale
sheaves on `p(y)`. -/
def restrictSmallEtaleSheaf_inverseImage (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) :
    restrictSmallEtaleSheaf
        (((toCartesianBasedFunctor f).morphismOfTopoiIn
            (StandardTopology.etale.overTopology S)).inverseImage.obj F)
        y ≅
      restrictSmallEtaleSheaf_reindex f y F :=
  ObjectProperty.isoMk _ (restrictSmallEtaleSheaf_inverseImage_presheaf f y F)

/-- On an étale neighborhood `V'`, the forward map of
`restrictSmallEtaleSheaf_inverseImage` is inverse-image evaluation followed by
`F` applied to the inverse cartesian fill-in. -/
theorem restrictSmallEtaleSheaf_inverseImage_hom_app (y : Y.total)
    (F : Sheaf X.etaleTopology (Type (u + 1))) (V' : (Y.p.obj y).left.Etale) :
    ((restrictSmallEtaleSheaf_inverseImage f y F).hom.hom.app (op V')) =
      restrictSmallEtaleSheaf_inverseImage_app_hom f y F V' :=
  rfl

end AlgebraicGeometry.GroupoidsOver
