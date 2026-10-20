module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite directed algebra approximations

This leaf refines a finite-type directed approximation by requiring each
stagewise ring homomorphism to be finite.  The finite-stage condition is kept
separate from the direct-limit presentation itself, so consumers can use the
least approximation structure matching their argument.
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A finite-type directed approximation whose stagewise ring homomorphisms
are finite. -/
@[stacks 0BTG "finite directed approximation"]
structure Finite (f : R →+* S) extends FiniteType f where
  /-- Each stagewise map is finite. -/
  mapFinite (i : index) : (map i).Finite

namespace Finite

variable {f : R →+* S}

/-- Refine a finite-type approximation by supplying finiteness of every
stage map. -/
@[stacks 0BTG "finite approximation constructor"]
def of (A : FiniteType f) (h : ∀ i : A.index, (A.map i).Finite) :
    Finite f where
  toFiniteType := A
  mapFinite := h

/-- Stacks 0BTG: an integral commutative-ring homomorphism admits a directed
finite approximation. -/
@[stacks 0BTG]
theorem nonempty_of_integral (f : R →+* S) (h_integral : f.IsIntegral) :
    Nonempty (Finite.{u, v, max u v, u, v} f) := sorry

end Finite

end Ring.DirectLimit.Algebra.Approximation
