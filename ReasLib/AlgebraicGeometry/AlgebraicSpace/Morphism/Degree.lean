/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Degree
public import Mathlib.Order.Lattice.Nat

/-!
# Degree of morphisms of integral algebraic spaces

The degree is the generic residue-field degree. Its total natural-number
extension is zero for infinite generic residue-field extensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The degree of a dominant locally finite type morphism of integral algebraic
spaces is its generic residue-field degree, with value zero for an infinite
extension. -/
noncomputable def degree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] : ℕ :=
  sSup ((fun x : Points X => residueDegree f x) '' genericPoints X)

/-- The generic residue-field extensions of a dominant morphism of integral
algebraic spaces are finite. -/
def FiniteResidueFieldExtension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Dominant f] : Prop :=
  ∀ ⦃x : Points X⦄, x ∈ genericPoints X → FiniteResidueFieldExtensionAt f x

/-- Finiteness of the generic residue-field extension is finite-dimensionality
of the algebra induced by `residueFieldMap` at any generic point. -/
theorem FiniteResidueFieldExtension_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    FiniteResidueFieldExtension f ↔
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      FiniteDimensional (Y.residueField (Points.map f x))
        (X.residueField x) :=
  sorry

/-- The degree of `f` equals the residue degree at any generic point of `X`. -/
theorem degree_eq_residueDegree {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    degree f = residueDegree f x :=
  sorry

/-- The degree of `f` is the finrank `[κ(x) : κ(y)]` at a generic point `x`. -/
theorem degree_eq_finrank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    degree f =
      -- Local instance justification (instance diamond): competing morphisms induce competing algebras on the same residue fields
      letI := (residueFieldMap f x).hom.toAlgebra
      Module.finrank (Y.residueField (Points.map f x)) (X.residueField x) :=
  sorry

/-- A dominant locally finite type morphism of integral algebraic spaces with
finite generic residue-field extension has positive degree. -/
theorem degree_pos {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [Dominant f] (hf : FiniteResidueFieldExtension f) : 0 < degree f :=
  sorry

/-- Finite residue-field extensions of integral algebraic spaces are closed
under composition of dominant morphisms. -/
theorem finiteResidueFieldExtension_comp {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g) :
    FiniteResidueFieldExtension (f ≫ g) :=
  sorry

/-- Degrees multiply under composition of dominant locally finite type morphisms
of integral algebraic spaces with finite generic residue-field extensions. -/
@[stacks 0ENH]
theorem degree_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Dominant f] [Dominant g]
    (hf : FiniteResidueFieldExtension f) (hg : FiniteResidueFieldExtension g) :
    degree (f ≫ g) = degree f * degree g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
