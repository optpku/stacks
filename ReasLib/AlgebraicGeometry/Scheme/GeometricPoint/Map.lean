/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint

variable {X Y : Scheme.{u}}

/-- Postcompose a geometric point with a morphism of schemes. -/
noncomputable def map (xbar : GeometricPoint X) (f : X ⟶ Y) : GeometricPoint Y where
  toFieldValuedPoint := xbar.toFieldValuedPoint.map f
  isAlgClosed := xbar.isAlgClosed

/-- The scheme morphism of a postcomposed geometric point is the evident composite. -/
theorem map_hom (xbar : GeometricPoint X) (f : X ⟶ Y) :
    (map xbar f).hom = xbar.hom ≫ f := sorry

/-- The image of a postcomposed geometric point is the image of its original point. -/
theorem map_image (xbar : GeometricPoint X) (f : X ⟶ Y) :
    (xbar.map f).image = f xbar.image := sorry

/-- Postcomposition preserves specialization of the images of geometric points. -/
theorem map_specializes {xbar' xbar : GeometricPoint X}
    (hSpec : Specializes xbar'.image xbar.image) (f : X ⟶ Y) :
    Specializes (xbar'.map f).image (xbar.map f).image := sorry

end AlgebraicGeometry.Scheme.GeometricPoint
