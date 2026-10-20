/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap10.Example_10_119_5
public import ReasLib.RingTheory.Normal.Nagata.DVR
import StacksCheckRecall

@[expose] public section

/-!
# Nagata discrete valuation rings

@stack 09E1

The generic DVR criterion is recalled from its canonical owner. The remaining declarations retain
the concrete coefficient-DVR example and the finite-extension obstruction from the source.
-/

universe u

open scoped PthPowerSubfield

/- Example 10.162.17 (1), tag `09E1`: a discrete valuation ring is Nagata
if and only if it is `N-2`. -/
@[stacks 09E1]
#check @NagataRing.iff_isN2Ring_of_discreteValuationRing

section

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

local notation "A" => finitePthPowerCoefficientSubring k p

-- Proof sketch: choose `f ∉ A` from Example `10.119.5`. If `A` were Nagata, then the finite
-- overring `A[f]` would also be Nagata by Proposition `10.162.16`; since `A[f]` is a local
-- domain, Lemma `10.162.13` would make it analytically unramified, contradicting Remark
-- `10.119.6`.
/-- Example 10.162.17 (2): if `k / k^p` is infinite, then the discrete valuation ring
`A := finitePthPowerCoefficientSubring k p` from Example `10.119.5` is not Nagata. -/
@[stacks 09E1]
theorem finitePthPowerCoefficientSubring_not_nagataRing
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ NagataRing ↥A := sorry

-- Proof sketch: combine the source-facing non-Nagata statement with part `(1)`.
/-- For the DVR `A := finitePthPowerCoefficientSubring k p` of Example `10.119.5`, infinite
`k / k^p` also forces failure of `N-2`. -/
theorem finitePthPowerCoefficientSubring_not_isN2Ring
    (hnfd : ¬ FiniteDimensional (k^[p]) k) :
    ¬ IsN2Ring ↥A := sorry

end

section

variable (A : Type u) [CommRing A]

-- Proof sketch: if `A` were Nagata, then in particular it would be `N-2` by the first clause.
-- The example argues that for the specific finite extension `A ⊂ R = A[f]`, the ring `R` is not
-- `N-1`; this contradicts the Nagata property for finite domain extensions.
/-- Companion reduction: a finite domain extension of a Nagata ring cannot fail `N-1`. -/
theorem discreteValuationRing_not_nagataRing_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ NagataRing A := sorry

section

variable [IsDomain A] [IsDiscreteValuationRing A]

-- Proof sketch: combine the previous theorem with
-- `NagataRing.iff_isN2Ring_of_discreteValuationRing`.
/-- A discrete valuation ring with a finite domain extension failing `N-1` is also not `N-2`. -/
theorem discreteValuationRing_not_isN2Ring_of_finite_extension_not_isN1Ring
    (R : Type u) [CommRing R] [IsDomain R] [Algebra A R] [Module.Finite A R]
    (hR : ¬ IsN1Ring R) :
    ¬ IsN2Ring A := sorry

end

end
