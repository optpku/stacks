module

public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-type quasi-finite algebras

Mathlib's `Algebra.QuasiFinite` deliberately records finite fibers without a
finite-type hypothesis. This module defines the conjunction of finite type
and finite-fibre quasi-finiteness, together with its primewise version.
-/

universe u v

namespace Algebra.FiniteType

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra is finite-type quasi-finite at a prime of `S` when it is of
finite type and its localization at that prime is quasi-finite over `R`. -/
@[stacks 00PL]
def QuasiFiniteAt (q : Ideal S) [q.IsPrime] : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFiniteAt R q

namespace QuasiFiniteAt

variable {R S}
variable {q : Ideal S} [q.IsPrime]

/-- The finite-type component of a finite-type quasi-finite-at-prime algebra. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.FiniteType R S := sorry

/-- The canonical Mathlib quasi-finite-at-prime component. -/
theorem toQuasiFiniteAt (h : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Algebra.QuasiFiniteAt R q := sorry

/-- An ambient finite-type algebra together with quasi-finiteness at a prime
gives finite-type quasi-finiteness at that prime. -/
theorem of_quasiFiniteAt [Algebra.FiniteType R S] (h : Algebra.QuasiFiniteAt R q) :
    Algebra.FiniteType.QuasiFiniteAt R S q := sorry

/-- Under a finite-type hypothesis, the finite-type and underlying primewise
quasi-finite predicates are equivalent. -/
theorem iff_quasiFiniteAt [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFiniteAt R S q ↔ Algebra.QuasiFiniteAt R q := sorry

end QuasiFiniteAt

/-- An `R`-algebra is finite-type quasi-finite when it is of finite type and
has finite fibres. -/
@[stacks 00PL]
def QuasiFinite : Prop :=
  Algebra.FiniteType R S ∧ Algebra.QuasiFinite R S

namespace QuasiFinite

variable {R S}

/-- The finite-type component of a finite-type quasi-finite algebra. -/
theorem finiteType (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.FiniteType R S := sorry

/-- The canonical Mathlib quasi-finite component. -/
theorem toQuasiFinite (h : Algebra.FiniteType.QuasiFinite R S) :
    Algebra.QuasiFinite R S := sorry

/-- An ambient finite-type algebra together with the quasi-finite condition
gives finite-type quasi-finiteness. -/
theorem of_quasiFinite [Algebra.FiniteType R S] (h : Algebra.QuasiFinite R S) :
    Algebra.FiniteType.QuasiFinite R S := sorry

/-- A module-finite algebra is finite type and quasi-finite. -/
theorem of_moduleFinite [Module.Finite R S] : Algebra.FiniteType.QuasiFinite R S := sorry

/-- Under a finite-type hypothesis, finite-type quasi-finiteness is equivalent
to the underlying quasi-finite predicate. -/
theorem iff_quasiFinite [Algebra.FiniteType R S] :
    Algebra.FiniteType.QuasiFinite R S ↔ Algebra.QuasiFinite R S := sorry

section Composition

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Composition preserves finite-type quasi-finiteness. -/
@[stacks 00PO "finite-type quasi-finite composition"]
theorem comp (hRS : Algebra.FiniteType.QuasiFinite R S)
    (hST : Algebra.FiniteType.QuasiFinite S T) :
    Algebra.FiniteType.QuasiFinite R T := sorry

end Composition

end QuasiFinite

end

end Algebra.FiniteType

namespace Algebra.QuasiFiniteAt

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a finite-type algebra over an Artinian ring, the quasi-finite locus in its prime
spectrum is finite. -/
@[stacks 00UK "finite quasi-finite locus"]
theorem finite_locus [IsArtinianRing R] [Algebra.FiniteType R S] :
    Set.Finite {q : PrimeSpectrum S | Algebra.QuasiFiniteAt R q.asIdeal} := sorry

/-- In a finite-type algebra, only finitely many primes over a fixed base prime are
quasi-finite. -/
@[stacks 00UK "finite quasi-finite fiber"]
theorem finite_primesOver [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    Set.Finite {q : p.primesOver S | Algebra.QuasiFiniteAt R q.1} := sorry

end

end Algebra.QuasiFiniteAt
