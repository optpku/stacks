/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber

/-!
# Residue-field maps of morphisms of algebraic spaces

A morphism of decent algebraic spaces induces residue-field homomorphisms from
its unique residue-point factorizations, including at points of a fixed fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace FieldValuedPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

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
  by
    have h := (subsingleton_residuePointFactor f x).elim
      (Classical.choice (exists_residuePointFactor f x)) φ
    dsimp only [residueFieldMap]
    rw [h]

/-- The residue-field morphism induced by a point of `f` over `y`. -/
def PointsOver.residueFieldMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (y : Points Y)
    (x : fiberOver f y) :
    Y.residueField y ⟶ X.residueField x :=
  Eq.ndrec (motive := fun z ↦ Y.residueField z ⟶ X.residueField (x : Points X))
    (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap f (x : Points X))
    x.property

end AlgebraicGeometry.AlgebraicSpace.Hom

open AlgebraicGeometry.AlgebraicSpace.Hom

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of decent algebraic spaces makes `κ(x)` into an algebra over
`κ(f(x))`. -/
instance residueFieldAlgebra {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Algebra (Y.residueField (Points.map f x)) (X.residueField x) :=
  (residueFieldMap f x).hom.toAlgebra

/-- The residue field at a point over `y` is naturally an algebra over `κ(y)`. -/
instance fiberResidueFieldAlgebra {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (y : Points Y)
    (x : fiberOver f y) :
    Algebra (Y.residueField y) (X.residueField x) :=
  (PointsOver.residueFieldMap f y x).hom.toAlgebra

end AlgebraicGeometry.AlgebraicSpace
