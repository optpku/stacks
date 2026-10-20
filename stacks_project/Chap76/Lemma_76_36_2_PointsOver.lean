/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism

/-!
# Point-set fibres and induced residue-field maps

The source-facing point-fibre abbreviation is retained for existing consumers.
The canonical fibre and residue-field maps are provided by shared owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace FieldValuedPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The set of points of `X` lying over a point `y` of `Y` under `f`. -/
abbrev pointsOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (y : Points Y) : Set (Points X) :=
  fiberOver f y

#check (AlgebraicGeometry.AlgebraicSpace.mem_fiberOver_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {y : Points Y} {x : Points X},
    x ∈ fiberOver f y ↔ Points.map f x = y)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    (f : X ⟶ Y) (x : Points X),
    Y.residueField (Points.map f x) ⟶ X.residueField x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.residueFieldMap_spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))),
    residueFieldMap f x =
      (Scheme.ΓSpecIso (Y.residueField (Points.map f x))).inv ≫
        φ.schemeHom.appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom)

#check (AlgebraicGeometry.AlgebraicSpace.residueFieldAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    (f : X ⟶ Y) (x : Points X),
    Algebra (Y.residueField (Points.map f x)) (X.residueField x))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.PointsOver.residueFieldMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    (f : X ⟶ Y) (y : Points Y) (x : fiberOver f y),
    Y.residueField y ⟶ X.residueField x)

#check (AlgebraicGeometry.AlgebraicSpace.fiberResidueFieldAlgebra :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    (f : X ⟶ Y) (y : Points Y) (x : fiberOver f y),
    Algebra (Y.residueField y) (X.residueField x))

end AlgebraicGeometry.AlgebraicSpace.Hom
