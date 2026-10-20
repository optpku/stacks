/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DescentData

/-!
# Pullback of algebraic-space descent data

A commutative square of algebraic spaces over a scheme `S` induces a functor between the
corresponding singleton-family categories of descent data. Different choices of the morphism
across the square give canonically naturally isomorphic functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}

/-- Pullback along a commutative square of algebraic spaces over `S` gives a functor on the
associated singleton-family categories of descent data. -/
noncomputable def functor (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f : Y' ⟶ Y) (sq : CommSq f a' a h) :
    DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a) ⥤
      DescentData (fun _ : PUnit.{v + 1} ↦ Y') (fun _ ↦ a') :=
  Pseudofunctor.DescentData.pullFunctor
    (p := h) (α := fun _ : PUnit.{v + 1} ↦ PUnit.unit) (p' := fun _ ↦ f)
    (overPseudofunctor S) (fun _ ↦ sq.w)

/-- The object underlying the pulled descent datum is the slice pullback of the original object
along the top morphism of the square. -/
theorem functor_obj_obj (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f : Y' ⟶ Y) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)) :
    ((functor a a' h f sq).obj D).obj PUnit.unit =
      (overPullback f).obj (D.obj PUnit.unit) := sorry

/-- The transition map obtained by pseudofunctorially pulling back the original transition map
around a commutative square. -/
noncomputable def transitionMap (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f : Y' ⟶ Y) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a))
    {Z : AlgebraicSpace S} (q : Z ⟶ X') (g₀ g₁ : Z ⟶ Y')
    (hg₀ : g₀ ≫ a' = q) (hg₁ : g₁ ≫ a' = q) :
    ((overPseudofunctor S).map g₀.op.toLoc).toFunctor.obj
        (((overPseudofunctor S).map f.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit)) ⟶
      ((overPseudofunctor S).map g₁.op.toLoc).toFunctor.obj
        (((overPseudofunctor S).map f.op.toLoc).toFunctor.obj
          (D.obj PUnit.unit)) :=
  Pseudofunctor.DescentData.pullFunctorObjHom
    (F := overPseudofunctor S) (f := fun _ : PUnit.{v + 1} ↦ a)
    (p := h) (f' := fun _ : PUnit.{v + 1} ↦ a')
    (α := fun _ : PUnit.{v + 1} ↦ PUnit.unit) (p' := fun _ ↦ f)
    (j₁ := PUnit.unit) (j₂ := PUnit.unit)
    (fun _ : PUnit.{v + 1} ↦ sq.w) D q g₀ g₁ hg₀ hg₁

/-- The transition map of the pulled datum is the canonical pullback transition map. -/
theorem functor_obj_hom (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f : Y' ⟶ Y) (sq : CommSq f a' a h)
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a))
    {Z : AlgebraicSpace S} (q : Z ⟶ X') (g₀ g₁ : Z ⟶ Y')
    (hg₀ : g₀ ≫ a' = q) (hg₁ : g₁ ≫ a' = q) :
    ((functor a a' h f sq).obj D).hom
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) q g₀ g₁ hg₀ hg₁ =
      transitionMap a a' h f sq D q g₀ g₁ hg₀ hg₁ := sorry

/-- Pullback maps a morphism of descent data by pulling back its unique component along the
top morphism of the square. -/
theorem functor_map_hom (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f : Y' ⟶ Y) (sq : CommSq f a' a h)
    {D E : DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)} (φ : D ⟶ E) :
    ((functor a a' h f sq).map φ).hom PUnit.unit =
      (overPullback f).map (φ.hom PUnit.unit) := sorry

/-- Two morphisms across the same commutative square boundary induce canonically naturally
isomorphic pullback functors on singleton-family descent data. -/
noncomputable def iso (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f₀ f₁ : Y' ⟶ Y) (sq₀ : CommSq f₀ a' a h) (sq₁ : CommSq f₁ a' a h) :
    functor a a' h f₀ sq₀ ≅ functor a a' h f₁ sq₁ :=
  Pseudofunctor.DescentData.pullFunctorIso (overPseudofunctor S)
    (fun _ : PUnit.{v + 1} ↦ sq₀.w) (fun _ : PUnit.{v + 1} ↦ sq₁.w)

/-- The component of the canonical comparison is the descent-data isomorphism between the
two pullbacks of the original unique component. -/
theorem iso_hom_app_hom (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X)
    (f₀ f₁ : Y' ⟶ Y) (sq₀ : CommSq f₀ a' a h) (sq₁ : CommSq f₁ a' a h)
    (D : DescentData (fun _ : PUnit.{v + 1} ↦ Y) (fun _ ↦ a)) :
    ((iso a a' h f₀ f₁ sq₀ sq₁).hom.app D).hom PUnit.unit =
      (D.iso (a' ≫ h) f₀ f₁ sq₀.w sq₁.w).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.DescentData.Pullback
