/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic

@[expose] public section

/-!
# Ramification of Discrete Valuation Ring Extensions

The ramification index is a convenient extension-level interface over
`Ideal.ramificationIdx` on the target maximal ideal. This module also records the
weakly unramified predicate and its computational ideal-theoretic API.

@stack 09E4
-/

universe u v

open Ideal IsLocalRing

namespace IsExtensionOfDiscreteValuationRings

section

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [IsDiscreteValuationRing B]

/-- The ramification index of an extension of discrete valuation rings. -/
@[stacks 09E4 "ramification index"]
noncomputable def ramificationIndex [IsExtensionOfDiscreteValuationRings A B] : ℕ :=
  (maximalIdeal B).ramificationIdx A

/-- The extension-level ramification index is the canonical one-ideal Mathlib ramification index
of the target maximal ideal over the source ring. -/
@[simp, stacks 09E4 "ramification index through the target maximal ideal"]
theorem ramificationIndex_eq_ramificationIdx [IsExtensionOfDiscreteValuationRings A B] :
    ramificationIndex A B = (maximalIdeal B).ramificationIdx A := sorry
-- Proof strategy: unfold `ramificationIndex`; it is definitionally Mathlib's one-ideal
-- `Ideal.ramificationIdx` at the target maximal ideal.

/-- An extension of discrete valuation rings is weakly unramified when its ramification index is
one. -/
@[stacks 09E4 "weakly unramified DVR extension"]
class WeaklyUnramified [IsExtensionOfDiscreteValuationRings A B] : Prop where
  /-- The ramification index of a weakly unramified extension is one. -/
  ramificationIndex_eq_one : ramificationIndex A B = 1

/-- The identity extension of a discrete valuation ring is weakly unramified. -/
instance WeaklyUnramified.instSelf (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] :
    WeaklyUnramified A A := sorry

/-- Characterization of weakly unramified extensions by their ramification index. -/
@[simp]
theorem weaklyUnramified_iff_ramificationIndex_eq_one
    [IsExtensionOfDiscreteValuationRings A B] :
    WeaklyUnramified A B ↔ ramificationIndex A B = 1 := sorry
-- Proof strategy: project `WeaklyUnramified.ramificationIndex_eq_one` in one direction and use
-- the class constructor with the displayed equality in the other.

/-- Weak unramifiedness expressed directly through Mathlib's one-ideal ramification index. -/
@[simp, stacks 09E4 "weakly unramified one-ideal criterion"]
theorem weaklyUnramified_iff_ramificationIdx_eq_one
    [IsExtensionOfDiscreteValuationRings A B] :
    WeaklyUnramified A B ↔ (maximalIdeal B).ramificationIdx A = 1 := sorry
-- Proof strategy: compose `weaklyUnramified_iff_ramificationIndex_eq_one` with
-- `ramificationIndex_eq_ramificationIdx`.

/-- The image of the source maximal ideal in a DVR extension is a power of the target maximal
ideal. -/
lemma mapped_maximalIdeal_eq_pow_maximalIdeal [IsExtensionOfDiscreteValuationRings A B] :
    ∃ n : ℕ, (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ n := sorry
-- Proof strategy: the local-hom field puts the mapped source maximal ideal below
-- `maximalIdeal B`, while algebra-map injectivity makes it nonzero. Classify this nonzero proper
-- ideal with `IsDiscreteValuationRing.idealOrderIsoENat`; finiteness of its order gives
-- `n : ℕ`, and `idealOrderIsoENat_symm_apply_coe` identifies it with `maximalIdeal B ^ n`.

/-- An identified maximal-ideal exponent is the ramification index. -/
lemma ramificationIndex_eq_of_map_maximalIdeal_eq_pow [IsExtensionOfDiscreteValuationRings A B]
    {n : ℕ} (hpow : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ n) :
    ramificationIndex A B = n := sorry
-- Proof strategy: rewrite with `ramificationIndex_eq_ramificationIdx` and
-- `Ideal.ramificationIdx_def`; replace the mapped ideal by `hpow`, then use the DVR formula for
-- the length of the quotient by `maximalIdeal B ^ n`.

/-- The exponent in a maximal-ideal power description of a DVR extension is positive. -/
lemma map_maximalIdeal_pow_exponent_pos [IsExtensionOfDiscreteValuationRings A B] {e : ℕ}
    (hpow : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e) :
    0 < e := sorry
-- Proof strategy: if `e = 0`, then `hpow` makes the mapped source maximal ideal equal to `⊤`.
-- This contradicts the local-hom inclusion of that image in the proper ideal `maximalIdeal B`.

/-- The ramification index is characterized by the image of the maximal ideal. -/
theorem ramificationIndex_eq_iff [IsExtensionOfDiscreteValuationRings A B] (e : ℕ) :
    ramificationIndex A B = e ↔
      0 < e ∧ (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e := sorry
-- Proof strategy: choose the exponent from `mapped_maximalIdeal_eq_pow_maximalIdeal`, identify it
-- with `ramificationIndex_eq_of_map_maximalIdeal_eq_pow`, and use
-- `map_maximalIdeal_pow_exponent_pos`; uniqueness follows by applying the ramification-index
-- equality to either power description.

/-- The ramification index of an extension of discrete valuation rings is positive. -/
theorem ramificationIndex_pos [IsExtensionOfDiscreteValuationRings A B] :
    0 < ramificationIndex A B := sorry
-- Proof strategy: obtain a maximal-ideal power description, identify its exponent with the
-- ramification index, and apply `map_maximalIdeal_pow_exponent_pos`.

/-- Weakly unramified extensions are exactly those whose maximal ideal maps onto the target
maximal ideal. -/
theorem weaklyUnramified_iff_map_maximalIdeal [IsExtensionOfDiscreteValuationRings A B] :
    WeaklyUnramified A B ↔
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := sorry
-- Proof strategy: combine `weaklyUnramified_iff_ramificationIndex_eq_one` with
-- `ramificationIndex_eq_iff A B 1` and simplify `maximalIdeal B ^ 1` and positivity of `1`.

namespace WeaklyUnramified

/-- A weakly unramified DVR extension maps the source maximal ideal onto the
target maximal ideal. -/
@[stacks 0BJ2 "DVR maximal ideal map"]
theorem map_maximalIdeal_eq [IsExtensionOfDiscreteValuationRings A B]
    [WeaklyUnramified A B] :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := sorry
-- Proof strategy: take the forward implication of
-- `weaklyUnramified_iff_map_maximalIdeal A B` using the ambient class instance.

end WeaklyUnramified

end

end IsExtensionOfDiscreteValuationRings
