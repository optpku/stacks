/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point.Jacobson
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

/-!
# Closed points of schemes over a field

This module records the finite-dimensionality of residue fields at closed points of schemes
locally of finite type over a field.
-/

@[expose] public section

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The residue field at a closed point of a scheme locally of finite type over a field is
finite-dimensional over the base field. -/
instance closedPointResidueFieldFiniteDimensional
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (x : closedPoints X.left) :
    FiniteDimensional k (X.left.residueField x.1) := sorry

/-- The residue field at a closed point of a scheme locally of finite type over a finite field
is finite. -/
instance closedPointResidueFieldFinite [Finite k]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (x : closedPoints X.left) :
    Finite (X.left.residueField x.1) :=
  Module.finite_of_finite k

/-- The residue field at a closed point of a scheme locally of finite type over a finite field
has a canonical classical finite enumeration. -/
instance closedPointResidueFieldFintype [Finite k]
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (x : closedPoints X.left) :
    Fintype (X.left.residueField x.1) :=
  Fintype.ofFinite _

/-- A closed point of a scheme locally of finite type over a field has relative dimension zero
for the dimension function induced from the constant-zero function on the spectrum of the field. -/
theorem closedPoint_relativeDimensionFunction_eq_zero
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] (x : closedPoints X.left) :
    X.hom.relativeDimensionFunction
      (fun _ : Spec (CommRingCat.of k) ↦ 0) x = 0 := sorry

end AlgebraicGeometry.SchemeOverField
