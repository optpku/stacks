module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Zero

@[expose] public section

universe u

namespace Derivation

/-- Self-valued derivations of a finite type algebra over a field are finite-dimensional exactly
when every prime ideal of the algebra is maximal. This predicate also covers the zero algebra. -/
theorem finiteDimensional_iff_krullDimLE_zero (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [Algebra.FiniteType k P] :
    FiniteDimensional k (Derivation k P P) ↔ Ring.KrullDimLE 0 P := sorry

/-- For a nontrivial finite type algebra over a field, self-valued derivations are
finite-dimensional exactly when its Krull dimension is zero. -/
theorem finiteDimensional_iff_ringKrullDim_eq_zero (k : Type u) [Field k] (P : Type u)
    [CommRing P] [Algebra k P] [Algebra.FiniteType k P] [Nontrivial P] :
    FiniteDimensional k (Derivation k P P) ↔ ringKrullDim P = 0 := by
  rw [finiteDimensional_iff_krullDimLE_zero, ringKrullDimZero_iff_ringKrullDim_eq_zero]

end Derivation
