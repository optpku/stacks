/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Height
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.Normal.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Reduced principal quotients of normal local domains

This leaf owns the existence of reduced principal hypersurface sections in a
Noetherian normal local domain.  Finite families of height-one primes are
represented by a `Finset` of prime-spectrum points, so distinctness is carried
by the collection rather than by a separate proof parameter.

@stack 0AXH
@stack 0AXI
-/

universe u

open IsLocalRing

namespace IsNormalRing

namespace ReducedPrincipalQuotient

variable {R : Type u} [CommRing R]
variable [IsNoetherianRing R] [IsLocalRing R] [IsNormalRing R]

/-- Lemma 15.126.5: in dimension two, a finite family of height-one primes in a Noetherian
normal local domain contains a common nonzero element whose principal quotient is reduced. -/
@[stacks 0AXH "Lemma 15.126.5, reduced principal quotient through height-one primes"]
theorem exists_mem_heightOne
    (hdim : ringKrullDim R = 2)
    (ps : Finset { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    ∃ f : R,
      f ≠ 0 ∧ (∀ p ∈ ps, f ∈ p.1.asIdeal) ∧
        IsReduced (R ⧸ principalIdeal f) := sorry
-- Proof strategy: choose a nonzero element in all primes of `ps` and complete
-- it to a stable two-parameter system.  Among admissible deep perturbations,
-- maximize the number of height-one branches of the principal ideal; the
-- one-dimensional branch-count bound makes this finite.  A symbolic-power
-- correction at the DVR localizations would otherwise increase the count, so
-- every branch has order one and the principal quotient is reduced.

/-- Every nonzero element in a two-dimensional Noetherian normal local domain divides a power
of a nonzero element defining a reduced principal quotient. -/
@[stacks 0AXI "reduced principal quotient controlling a nonzero element"]
theorem exists_dvd_pow
    (hdim : ringKrullDim R = 2) (a : R) (ha : a ≠ 0) :
    ∃ c : R,
      c ≠ 0 ∧ IsReduced (R ⧸ principalIdeal c) ∧
        ∃ n : ℕ, a ∣ c ^ n := sorry
-- Proof strategy: enumerate the minimal primes over `principalIdeal a`; the
-- principal ideal theorem makes them height one.  Apply `exists_mem_heightOne`
-- to this finite family.  The resulting `c` belongs to every minimal prime over
-- `(a)`, hence to its radical; `Ideal.mem_radical_iff` supplies `n` with
-- `c ^ n ∈ (a)`, which is the required divisibility.

/-- Lemma 15.126.6: maximal-ideal form of the reduced principal-quotient power bound. -/
@[stacks 0AXI "Lemma 15.126.6, reduced principal quotient power bound"]
theorem exists_dvd_pow_of_mem_maximalIdeal
    (hdim : ringKrullDim R = 2) (a : maximalIdeal R) (ha : (a : R) ≠ 0) :
    ∃ c : R,
      c ≠ 0 ∧ IsReduced (R ⧸ principalIdeal c) ∧
        ∃ n : ℕ, (a : R) ∣ c ^ n := sorry
-- Proof strategy: apply `exists_dvd_pow` to the underlying ring element of
-- `a`; the maximal-ideal packaging adds no further obligation.

end ReducedPrincipalQuotient

end IsNormalRing
