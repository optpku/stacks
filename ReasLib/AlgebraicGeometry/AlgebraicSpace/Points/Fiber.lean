/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback

/-!
# Set-theoretic fibres of morphisms of algebraic spaces

The fibre of a morphism `f : X ⟶ Y` of algebraic spaces over a point `y` of
`Y` is the preimage of `{y}` under the induced map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The set-theoretic fibre of a morphism of algebraic spaces over a point of the
target, as a subset of `Points X` with the induced topology. -/
def fiberOver (f : X ⟶ Y) (y : Points Y) : Set (Points X) :=
  Points.map f ⁻¹' {y}

/-- Membership in the set-theoretic fibre is the equation on points. -/
theorem mem_fiberOver_iff (f : X ⟶ Y) {y : Points Y} {x : Points X} :
    x ∈ fiberOver f y ↔ Points.map f x = y :=
  sorry

/-- The set-theoretic fibre is the singleton preimage of the given point. -/
theorem fiberOver_eq (f : X ⟶ Y) (y : Points Y) :
    fiberOver f y = Points.map f ⁻¹' {y} :=
  sorry

/-- Replacing the point by the class of a field-valued representative does not
change the set-theoretic fibre. -/
theorem fiberOver_eq_of_mk (f : X ⟶ Y) (p : FieldValuedPoint Y) {y : Points Y}
    (hy : Points.mk p = y) :
    fiberOver f y = fiberOver f (Points.mk p) :=
  sorry

/-- The canonical map on points from the field-valued fibre lands in the
set-theoretic fibre over the class of `p`. -/
theorem mapsTo_fieldFiberι_fiberOver (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    Set.MapsTo (Points.map (fieldFiberι f p)) Set.univ
      (fiberOver f (Points.mk p)) :=
  sorry

/-- The canonical map on points from the field-valued fibre is surjective onto
the set-theoretic fibre over the class of `p`. -/
theorem surjOn_pointsMap_fieldFiberι (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    Set.SurjOn (Points.map (fieldFiberι f p)) Set.univ
      (fiberOver f (Points.mk p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
