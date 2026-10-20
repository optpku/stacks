/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map

/-!
# Cartesian base change of geometric lifts

A cartesian square identifies lifts of a geometric point with lifts of its
image, preserving the source field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint.Fiber

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)

/-- A cartesian square identifies same-field geometric lifts over the two bases. -/
def baseChangeEquiv (ybar' : GeometricPoint Y') :
    Fiber f' ybar' ≃ Fiber f (ybar'.map g) where
  toFun x' := ⟨x'.lift ≫ g', sorry⟩
  invFun x :=
    ⟨h_cart.lift x.lift ybar'.hom (x.fac.trans (GeometricPoint.map_hom ybar' g)),
      sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The forward map on geometric lifts is postcomposition with the top arrow. -/
theorem baseChangeEquiv_apply (ybar' : GeometricPoint Y')
    (x' : Fiber f' ybar') :
    (baseChangeEquiv f g f' g' h_cart ybar' x').lift = x'.lift ≫ g' :=
  rfl

/-- The inverse map on geometric lifts is the cartesian lift of the two morphisms. -/
theorem baseChangeEquiv_symm_apply (ybar' : GeometricPoint Y')
    (x : Fiber f (ybar'.map g)) :
    ((baseChangeEquiv f g f' g' h_cart ybar').symm x).lift =
      h_cart.lift x.lift ybar'.hom
        (x.fac.trans (GeometricPoint.map_hom ybar' g)) :=
  rfl

/-- Postcomposing a cartesian geometric lift recovers the original geometric point. -/
theorem baseChangeEquiv_symm_point (ybar' : GeometricPoint Y')
    (x : Fiber f (ybar'.map g)) :
    (((baseChangeEquiv f g f' g' h_cart ybar').symm x).point).map g' =
      x.point :=
  sorry

end AlgebraicGeometry.Scheme.GeometricPoint.Fiber

end
