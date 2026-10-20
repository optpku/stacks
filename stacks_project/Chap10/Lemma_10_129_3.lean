/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.RingTheory.LocalRing.BuchsbaumEisenbud
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.BaseChange
import StacksCheckRecall

/-!
@stack 00RB
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {e : ℕ}

variable [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]

-- Proof sketch: apply the Buchsbaum--Eisenbud exactness criterion on each local fiber ring to
-- translate exactness of the fiber complex into determinantal-ideal conditions. Flatness lets one
-- compare the localized complex with the residue-fiber complex, and Lemma `10.129.2` makes the
-- required regular-sequence conditions open under the assumption that all fibers are
-- Cohen--Macaulay of constant Krull dimension.
namespace FiniteFreeComplex

/-- Lemma 10.129.3: let `R → S` be a finite type flat ring map with `R` Noetherian, and let
`C : FiniteFreeComplex S e` encode a finite complex `0 → S^{n_e} → ⋯ → S^{n_0}`. If there is a
constant such that every fiber ring `κ(𝔭) ⊗[R] S` is Cohen--Macaulay of that Krull dimension,
then the set of primes `q : Spec(S)` for which the scalar extension of `C` to the fiber local
ring at `q` is exact in positive degrees is an open subset of `Spec(S)`. -/
@[stacks 00RB]
theorem isOpen_baseChange_exactInPositiveDegrees (C : FiniteFreeComplex S e)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hConstDim : ∀ p p' : PrimeSpectrum R,
      ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (p'.asIdeal.Fiber S)) :
    IsOpen {q : PrimeSpectrum S |
      (C.baseChange (fiberLocalRingAt R S q)).ExactInPositiveDegrees} := sorry

end FiniteFreeComplex

@[stacks 00RB "finite-free scalar extension owner"]
#check @FiniteFreeComplex.baseChange

@[stacks 00RB "underlying scalar-extended complex"]
#check @FiniteFreeComplex.baseChangeComplex

#check @FiniteFreeComplex.isOpen_baseChange_exactInPositiveDegrees

end
