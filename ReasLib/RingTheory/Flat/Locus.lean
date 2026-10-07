module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Localization.AtPrime

/-!
# Flatness Loci of Modules

The set of target primes where a module is flat over a fixed base ring, together with pointwise
and finite-presentation criteria.
-/

@[expose] public section

universe u v w

namespace Module

section Basic

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The locus in `Spec(S)` where the localization of `M` is flat over the fixed base ring `R`. -/
@[stacks 00RC "flatness locus over a base ring"]
def flatOverBaseLocus : Set (PrimeSpectrum S) :=
  { q | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) }

/-- Membership in the flatness locus is flatness of the localized module over the original base
ring. -/
@[stacks 00RC "membership in the flatness locus", simp]
theorem mem_flatOverBaseLocus (q : PrimeSpectrum S) :
    q ∈ flatOverBaseLocus R S M ↔
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := sorry

/-- The flatness-locus condition can equivalently be expressed over the local base ring below
the target prime. -/
@[stacks 00RC "relative membership in the flatness locus"]
theorem mem_flatOverBaseLocus_iff_flatAtPrimeOver (q : PrimeSpectrum S) :
    q ∈ flatOverBaseLocus R S M ↔ Module.Flat.AtPrimeOver (R := R) (M := M) q := sorry

/-- A globally flat module has the whole target spectrum as its flatness locus. -/
@[stacks 00RC "flatness locus of a flat module"]
theorem flatOverBaseLocus_eq_univ_of_flat (hM : Module.Flat R M) :
    flatOverBaseLocus R S M = Set.univ := sorry

/-- If the localization of `M` away from `f` is flat over `R`, the corresponding basic open lies
inside the flatness locus. -/
@[stacks 00RC "basic open in a flatness locus"]
theorem basicOpen_subset_flatOverBaseLocus_of_flat_away {f : S}
    (hM : Module.Flat R (LocalizedModule.Away f M)) :
    (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) ⊆ flatOverBaseLocus R S M := sorry

end Basic

section FinitePresentation

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]

/-- The flatness locus of a finitely presented module over a finitely presented algebra is
open. -/
@[stacks 00RC "openness of the flatness locus"]
theorem isOpen_flatOverBaseLocus_of_finitePresentation :
    IsOpen (flatOverBaseLocus R S M) := sorry

end FinitePresentation

end Module
