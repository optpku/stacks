/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

universe u v

/-- A finite-dimensional domain algebra over a field is a field. -/
theorem FiniteDimensional.isField_of_domain (k : Type u) [Field k] (R : Type v) [CommRing R]
    [IsDomain R] [Algebra k R] [FiniteDimensional k R] : IsField R :=
  sorry
