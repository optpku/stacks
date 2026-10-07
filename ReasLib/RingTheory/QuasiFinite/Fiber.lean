module

public import ReasLib.RingTheory.QuasiFinite.Localization
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.RingTheory.QuasiFinite.Fiber.Dimension
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.KrullDimension.FiniteType.ZeroDimensional

@[expose] public section

/-!
# Quasi-finite residue-field fibers

@stack 0H8X
@stack 00PL

This leaf records consequences of quasi-finiteness for the residue-field
fiber over a selected prime. It is separate from the generic fiber library:
the statements here depend essentially on `Algebra.QuasiFinite`.
-/

universe u v

namespace Algebra.QuasiFiniteAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- For a finite-type algebra, quasi-finiteness at a prime is equivalent to
quasi-finiteness at its canonical prime in the residue-field fiber over its
specified contraction. -/
@[stacks 0H8X "quasi-finiteness at a residue-field fiber prime"]
theorem iff_fiberPrime [Algebra.FiniteType R S]
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField
        (PrimeSpectrum.fiberPrime p q hq).asIdeal := by
  constructor
  · intro h
    letI : Algebra.QuasiFiniteAt R q.asIdeal := h
    exact Algebra.QuasiFiniteAt.baseChange q.asIdeal
      (PrimeSpectrum.fiberPrime p q hq).asIdeal
      (by simpa using (PrimeSpectrum.fiberPrime_comap_asIdeal p q hq).symm)
  · intro h
    letI : q.asIdeal.LiesOver p.asIdeal :=
      ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
    letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField
        (PrimeSpectrum.fiberPrime p q hq).asIdeal := h
    exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
      p.asIdeal q.asIdeal (PrimeSpectrum.fiberPrime p q hq).asIdeal
      (by simpa using PrimeSpectrum.fiberPrime_comap_asIdeal p q hq)

/-- For a finite-type algebra, quasi-finiteness at `q` is equivalent to
quasi-finiteness at the canonical fiber prime over the contraction of `q`. -/
@[stacks 0H8X "quasi-finiteness at the canonical fiber prime"]
theorem iff_fiberPrimeAt [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    Algebra.QuasiFiniteAt R q.asIdeal ↔
      Algebra.QuasiFiniteAt (q.asIdeal.under R).ResidueField
        (fiberPrimeAt R S q).asIdeal := by
  change Algebra.QuasiFiniteAt R q.asIdeal ↔
    Algebra.QuasiFiniteAt
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField
      (PrimeSpectrum.fiberPrime
        (PrimeSpectrum.comap (algebraMap R S) q) q rfl).asIdeal
  exact iff_fiberPrime (PrimeSpectrum.comap (algebraMap R S) q) q rfl

end Algebra.QuasiFiniteAt

namespace Algebra.FiniteType

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- For a finite-type algebra, quasi-finiteness at every prime over `p`,
module-finiteness of the residue-field fiber, and finiteness of its prime
spectrum are equivalent. -/
@[stacks 0H8X "quasi-finite residue-field fiber criteria"]
theorem quasiFiniteAt_fiberTFAE (p : PrimeSpectrum R) :
    List.TFAE
      [ (∀ q : PrimeSpectrum S,
            PrimeSpectrum.comap (algebraMap R S) q = p →
              Algebra.QuasiFiniteAt R q.asIdeal),
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S),
        Finite (PrimeSpectrum (p.asIdeal.Fiber S)) ] := by
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have hqf_discrete :
      (∀ q : PrimeSpectrum S,
          PrimeSpectrum.comap (algebraMap R S) q = p →
            Algebra.QuasiFiniteAt R q.asIdeal) ↔
        DiscreteTopology (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    rw [← e.discreteTopology_iff, discreteTopology_iff_isOpen_singleton]
    constructor
    · intro h q
      rcases q with ⟨q, hq⟩
      subst p
      simpa using
        (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber q).mp (h q rfl)
    · intro h q hq
      subst p
      apply (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber q).mpr
      simpa using h ⟨q, rfl⟩
  have hzero := Algebra.FiniteType.zeroDimensionalTFAE
    (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S)
  tfae_have 1 ↔ 3 := hqf_discrete.trans (hzero.out 6 1 rfl rfl)
  tfae_have 2 ↔ 3 := by
    simpa using (hzero.out 4 1 rfl rfl)
  tfae_finish

end Algebra.FiniteType

namespace Algebra.QuasiFinite

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A quasi-finite algebra whose primes over `p` are all non-quasi-finite at
their corresponding target primes has a subsingleton residue-field fiber over
`p`. -/
@[stacks 00PL "empty quasi-finite fiber"]
theorem subsingletonFiber_of_forall_not_quasiFiniteAt
    [Algebra.QuasiFinite R S] (p : Ideal R) [p.IsPrime]
    (h : ∀ q : p.primesOver S, ¬ Algebra.QuasiFiniteAt R q.1) :
    Subsingleton (p.Fiber S) := sorry

end Algebra.QuasiFinite
