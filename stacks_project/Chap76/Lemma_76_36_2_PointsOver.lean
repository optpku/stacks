/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap68.Lemma_68_11_3

/-!
# Point-set fibres of morphisms of algebraic spaces

The ordinary point fibre of a morphism of algebraic spaces is the preimage of a
point under `Points.map`. On decent spaces, the unique residue-point
factorization supplies a residue-field homomorphism, and hence an algebra
structure on `κ(x)` over `κ(f(x))`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace FieldValuedPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The set of points of `X` lying over a point `y` of `Y` under `f`. -/
def pointsOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) : Set (Points X) :=
  Points.map f ⁻¹' {y}

/-- Membership in the point fibre is the equation saying that the point maps to
the chosen target point. -/
@[simp]
theorem mem_pointsOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) (x : Points X) :
    x ∈ pointsOver f y ↔ Points.map f x = y :=
  sorry

namespace PointsOver

/-- A point in `f.pointsOver y` maps to `y`. -/
@[simp]
theorem map_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) (x : pointsOver f y) :
    Points.map f x = y :=
  sorry

end PointsOver

/-- The residue-field homomorphism `κ(f(x)) ⟶ κ(x)` induced by a morphism of
decent algebraic spaces, extracted from the unique residue-point factorization
via global sections of source field spectra. -/
def residueFieldMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Y.residueField (Points.map f x) ⟶ X.residueField x :=
  (Scheme.ΓSpecIso (Y.residueField (Points.map f x))).inv ≫
    (Classical.choice (exists_residuePointFactor f x)).schemeHom.appTop ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom

/-- `residueFieldMap f x` is the global-sections map of the unique residue-point
factorization of `(residuePoint x).map f` through `residuePoint (Points.map f x)`. -/
theorem residueFieldMap_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :
    residueFieldMap f x =
      (Scheme.ΓSpecIso (Y.residueField (Points.map f x))).inv ≫
        φ.schemeHom.appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom :=
  sorry

/-- A morphism of decent algebraic spaces makes `κ(x)` into an algebra over
`κ(f(x))`. -/
instance residueFieldAlgebra {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Algebra (Y.residueField (Points.map f x)) (X.residueField x) :=
  (residueFieldMap f x).hom.toAlgebra

/-- The residue-field morphism induced by a point of `f` over `y`. -/
def PointsOver.residueFieldMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (y : Points Y)
    (x : pointsOver f y) :
    Y.residueField y ⟶ X.residueField x :=
  Eq.ndrec (motive := fun z ↦ Y.residueField z ⟶ X.residueField (x : Points X))
    (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap f (x : Points X))
    x.property

namespace PointsOver

/-- The residue field at a point over `y` is naturally an algebra over `κ(y)`. -/
instance residueFieldAlgebra {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (y : Points Y)
    (x : pointsOver f y) :
    Algebra (Y.residueField y) (X.residueField x) :=
  (residueFieldMap f y x).hom.toAlgebra

end PointsOver

end AlgebraicGeometry.AlgebraicSpace.Hom
