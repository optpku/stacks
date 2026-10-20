/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism.Laws
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Residue degrees of morphisms of algebraic spaces

The residue degree at a point is the dimension of its residue field over the
residue field of its image, with value zero for infinite extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The residue degree of `f` at `x` is the finrank of `κ(x)` over `κ(f(x))`,
or `0` if the extension is infinite. -/
noncomputable def residueDegree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) : ℕ :=
  -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
  letI := (residueFieldMap f x).hom.toAlgebra
  Module.finrank (Y.residueField (Points.map f x)) (X.residueField x)

/-- The residue degree is the finrank of the algebra induced by
`residueFieldMap`. -/
theorem residueDegree_eq_finrank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    residueDegree f x =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x) :=
  rfl

/-- The identity morphism has residue degree `1` at every point. -/
theorem residueDegree_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) : residueDegree (𝟙 X) x = 1 :=
  sorry

/-- Residue degrees multiply along a tower of residue-field extensions of
decent algebraic spaces. -/
theorem residueDegree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) :
    residueDegree (f ≫ g) x =
      residueDegree f x * residueDegree g (Points.map f x) :=
  sorry

/-- The residue-field extension of `f` at `x` is finite. -/
def FiniteResidueFieldExtensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) : Prop :=
  -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
  letI := (residueFieldMap f x).hom.toAlgebra
  FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)

/-- Finiteness of the residue-field extension at `x` is finite-dimensionality
of the algebra induced by `residueFieldMap`. -/
theorem FiniteResidueFieldExtensionAt_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y] (f : X ⟶ Y)
    (x : Points X) :
    FiniteResidueFieldExtensionAt f x ↔
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      FiniteDimensional (Y.residueField (Points.map f x))
        (X.residueField x) :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
