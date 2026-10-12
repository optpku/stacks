/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Relative dimension of an algebra at a prime

This leaf owns relative dimension as the local topological Krull dimension of the
residue-field fiber through a prime.  The definition is deliberately independent of
finite-type, Noetherian, and local hypotheses; more specialized dimension results belong in
separate leaves.
-/

noncomputable section

universe u v

section

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S]

/-- The relative dimension of `S/R` at `q`, computed using a specified `R`-algebra structure on
`S`, is the local topological Krull dimension at the fiber prime selected by `q`. -/
noncomputable abbrev relativeDimensionAtWith
    (algebra : Algebra R S) (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  topologicalKrullDimAt (@fiberPrimeAt R _ S _ algebra q)

variable [Algebra R S]

/-- The relative dimension of `S/R` at `q` is the local topological Krull dimension of the
residue-field fiber at the fiber prime selected by `q`. -/
@[stacks 00QD "relative dimension at a prime"]
noncomputable abbrev relativeDimensionAt (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  relativeDimensionAtWith R S inferInstance q

/-- The relative dimension of `S/R` is the supremum of its relative dimensions at target
primes. -/
@[stacks 00QD "global relative dimension"]
noncomputable abbrev relativeDimension : WithBot ℕ∞ :=
  ⨆ q : PrimeSpectrum S, relativeDimensionAt R S q

/-- The bounded relative-dimension locus in `Spec(S)`. -/
@[stacks 00QH "bounded relative-dimension locus"]
def relativeDimensionAtLELocus (n : ℕ) : Set (PrimeSpectrum S) :=
  {q : PrimeSpectrum S | relativeDimensionAt R S q ≤ (n : WithBot ℕ∞)}

/-- Membership in the bounded relative-dimension locus is the corresponding pointwise bound. -/
@[stacks 00QH "membership in the bounded relative-dimension locus"]
theorem mem_relativeDimensionAtLELocus (n : ℕ) (q : PrimeSpectrum S) :
    q ∈ relativeDimensionAtLELocus R S n ↔
      relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) := sorry

/-- Relative dimension at a point is bounded above by the Krull dimension of its whole
residue-field fiber. -/
@[stacks 00QD "relative dimension bounded by fiber dimension"]
theorem relativeDimensionAt_le_ringKrullDim_fiber (q : PrimeSpectrum S) :
    relativeDimensionAt R S q ≤ ringKrullDim ((q.asIdeal.under R).Fiber S) := sorry

end
