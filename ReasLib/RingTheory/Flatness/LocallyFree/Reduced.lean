module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber-Rank Criteria over Reduced Rings

This leaf names the residue-field fiber rank of a module over a commutative
ring.  It separates that rank from `Module.rankAtStalk`, whose agreement with
the fiber rank requires finite flatness, and records the reduced-ring
projectivity criterion in terms of the former.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The natural-number rank of the residue-field fiber of `M` at a prime. -/
noncomputable def fiberFinrank (N : Type v) [AddCommGroup N] [Module R N]
    (p : PrimeSpectrum R) : ℕ :=
  Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber N)

/-- The integer-valued residue-field fiber-rank function of `M`. -/
noncomputable def fiberRank (N : Type v) [AddCommGroup N] [Module R N]
    (p : PrimeSpectrum R) : ℤ :=
  (fiberFinrank N p : ℤ)

/-- The integer-valued fiber rank is the coercion of the natural-valued fiber rank. -/
@[simp]
theorem fiberRank_eq_intCast_fiberFinrank (N : Type v) [AddCommGroup N] [Module R N]
    (p : PrimeSpectrum R) :
    fiberRank N p = (fiberFinrank N p : ℤ) := sorry

/-- For a finite flat module, the residue-field fiber rank equals the stalk rank. -/
theorem fiberFinrank_eq_rankAtStalk [Module.Finite R M] [Flat R M] (p : PrimeSpectrum R) :
    fiberFinrank M p = rankAtStalk (R := R) M p := sorry

/-- For a finite flat module, the integer-valued fiber rank is the coercion of the stalk rank. -/
theorem fiberRank_eq_intCast_rankAtStalk [Module.Finite R M] [Flat R M] (p : PrimeSpectrum R) :
    fiberRank M p = (rankAtStalk (R := R) M p : ℤ) := sorry

/-- Over a reduced ring, a finite module is projective exactly when its
residue-field fiber-rank function is locally constant. -/
@[stacks 0FWG "finite projectivity from locally constant fiber rank"]
theorem projective_iff_isLocallyConstant_fiberRank [IsReduced R] [Module.Finite R M] :
    Projective R M ↔ IsLocallyConstant (fiberRank (R := R) M) := sorry

end Module
