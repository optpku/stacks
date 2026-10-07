module

public import ReasLib.Algebra.Module.FiniteLength.Determinant
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Dimension of the determinant space of a finite-length module

This file records cardinal- and natural-valued dimension bounds for the determinant space of a
finite-length module over a local ring.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/-- The determinant space of a finite-length module over a local ring has cardinal dimension at
most one over the residue field. -/
theorem rank_le_one (hM : IsFiniteLength R M) :
    Module.rank (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) ≤ 1 := sorry

/-- The determinant space of a finite-length module is finite-dimensional. -/
instance instFinite (hM : IsFiniteLength R M) :
    Module.Finite (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) := sorry

/-- The natural-valued dimension of the determinant space is at most one. -/
theorem finrank_le_one (hM : IsFiniteLength R M) :
    Module.finrank (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) ≤ 1 := sorry

/-- A finite-length determinant line has dimension one over the residue field. -/
theorem finrank_eq_one {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.finrank (IsLocalRing.ResidueField R)
      (Module.FiniteLengthDeterminant R M hM) = 1 := sorry

end Module.FiniteLengthDeterminant
