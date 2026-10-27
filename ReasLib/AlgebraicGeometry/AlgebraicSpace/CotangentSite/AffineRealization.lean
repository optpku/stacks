/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentSite.Category

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Cotangent
variable (Λ : CommRingCat.{u}) (X : AlgebraicSpace (Spec Λ))

/-- The functor sending a polynomial affine presentation to its affine target scheme. -/
def affineScheme : category Λ X ⥤ Scheme.{u} where
  obj x := x.right.obj.left
  map f := f.right.hom.left
  map_id := by intro _; rfl
  map_comp := by intros; simp

/-- The affine realization of a presentation is its target scheme. -/
theorem affineScheme_obj (x : category Λ X) :
    (affineScheme Λ X).obj x = x.right.obj.left := rfl

/-- Affine realization sends a morphism of presentations to its target-scheme morphism. -/
theorem affineScheme_map {x y : category Λ X} (f : x ⟶ y) :
    (affineScheme Λ X).map f = f.right.hom.left := rfl

/-- The scheme morphism from the étale chart of a presentation to its affine target. -/
def homToAffine (x : category Λ X) :
    ((smallEtaleToOver X).obj x.left).left ⟶ x.right.obj.left := x.hom.left

/-- The chart-to-affine morphism is the underlying scheme morphism of the presentation. -/
theorem homToAffine_eq_hom_left (x : category Λ X) :
    homToAffine Λ X x = x.hom.left := rfl

/-- The chart-to-affine morphism commutes with the structure morphisms to `Spec Λ`. -/
theorem homToAffine_over (x : category Λ X) :
    homToAffine Λ X x ≫ x.right.obj.hom = ((smallEtaleToOver X).obj x.left).hom := sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
