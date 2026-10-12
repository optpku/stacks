/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

@[expose] public section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- On a smooth scheme over a field, the closed points with finite-dimensional separable
residue field are dense. -/
theorem dense_closedPoints_finiteSeparableResidueField_of_smooth
    (X : SchemeOverField k) [Smooth X.hom] :
    Dense ({x : X.left | x ∈ closedPoints X.left ∧
      FiniteDimensional k (X.left.residueField x) ∧
        Algebra.IsSeparable k (X.left.residueField x)} : Set X.left) := sorry

end AlgebraicGeometry.SchemeOverField
