module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of directed algebra approximations

This leaf contains the producer theorems for the canonical finite-type
approximation owner. Property refinements such as bijective stage base change
are stated separately, so module and property-specific consumers can start
from the least structure they need.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit.Algebra.Approximation.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Stacks 00QY: every commutative-ring homomorphism has a directed
finite-type approximation. -/
@[stacks 00QY]
theorem nonempty (f : R →+* S) :
    Nonempty (FiniteType f) := sorry

/-- A finite-type commutative-ring homomorphism has a directed finite-type
approximation whose stage base-change maps are surjective. -/
@[stacks 00QZ "finite-type approximation"]
theorem exists_of_finiteType (f : R →+* S) (h_finiteType : f.FiniteType) :
    ∃ A : FiniteType f, A.toHom.baseChange_surjective := sorry

/-- A finitely presented ring homomorphism has a directed finite-type
approximation whose stage base-change maps are all bijective. -/
@[stacks 00R0 "finite-presentation approximation"]
theorem exists_of_finitePresentation (f : R →+* S) (h_finitePresentation : f.FinitePresentation) :
    ∃ A : FiniteType f, A.toHom.baseChange_bijective := sorry

end Ring.DirectLimit.Algebra.Approximation.FiniteType
