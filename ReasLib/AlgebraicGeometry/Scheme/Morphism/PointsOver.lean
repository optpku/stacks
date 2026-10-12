/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Points over a point of a scheme morphism

This leaf distinguishes the ordinary point fiber of a scheme morphism from its
scheme-theoretic fiber.  It provides the residue-field algebra attached to a
point in that ordinary fiber.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The set of points of `X` lying over a point `y` of `Y` under `f`. -/
def pointsOver (f : X ⟶ Y) (y : Y) : Set X :=
  {x | f x = y}

/-- Membership in the point fiber is the equation saying that the point maps
to the chosen target point. -/
@[simp]
theorem mem_pointsOver (f : X ⟶ Y) (y : Y) (x : X) :
    x ∈ f.pointsOver y ↔ f x = y := sorry

namespace PointsOver

/-- A point in `f.pointsOver y` maps to `y`. -/
@[simp]
theorem map_eq (f : X ⟶ Y) (y : Y) (x : f.pointsOver y) :
    f x = y := sorry

/-- The residue-field morphism induced by a point of `f` over `y`. -/
noncomputable def residueFieldMap
    (f : X ⟶ Y) (y : Y) (x : f.pointsOver y) :
    CommRingCat.of (Y.residueField y) ⟶ CommRingCat.of (X.residueField x) :=
  Eq.ndrec
    (motive := fun z ↦
      CommRingCat.of (Y.residueField z) ⟶ CommRingCat.of (X.residueField x))
    (f.residueFieldMap x) x.2

/-- The residue field at a point over `y` is naturally an algebra over
`κ(y)`. -/
noncomputable instance residueFieldAlgebra
    (f : X ⟶ Y) (y : Y) (x : f.pointsOver y) :
    Algebra (Y.residueField y) (X.residueField x) :=
  (residueFieldMap f y x).hom.toAlgebra

end PointsOver

end AlgebraicGeometry.Scheme.Hom
