/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Regular.GRing.CompleteLocal
public import ReasLib.RingTheory.Regular.GRing.EssentialFiniteness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal fibers of a polynomial ring over a complete local domain

@stack 07PU
-/

@[expose] public section

noncomputable section

open Algebra IsLocalRing
open scoped Polynomial

universe u v

/-- Lemma 15.50.9: let `A` be a Noetherian complete local domain with fraction field `K` of
prime characteristic. If `q ⊂ A[X]` is maximal over the maximal ideal of `A` and
`0 ≠ r ⊆ q` lies over `0 ⊂ A`, then the formal fiber at `(r, q)` is geometrically regular. -/
@[stacks 07PU "polynomial formal fiber over a complete local domain"]
theorem IsCompleteLocalRing.polynomial_formalFiber_isGeometricallyRegular
    {A : Type u} {K : Type v} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsCompleteLocalRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (q : MaximalSpectrum A[X]) (r : PrimeSpectrum A[X])
    (hq : q.asIdeal.comap (algebraMap A A[X]) = maximalIdeal A)
    (hr_ne : r.asIdeal ≠ ⊥)
    (hr_over : r.asIdeal.comap (algebraMap A A[X]) = ⊥)
    (hr_le : r.asIdeal ≤ q.asIdeal) :
    IsGeometricallyRegular r.asIdeal.ResidueField
      (r.asIdeal.Fiber (R̂[q.toPrimeSpectrum])) := sorry
