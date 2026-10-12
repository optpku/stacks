/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Henselian.Pair.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic properties of pair Henselization

This file owns the flatness, distinguished-ideal, and infinitesimal-quotient API for the chosen
Henselization of a commutative-ring pair.

@stack 0AGU
-/

@[expose] public section

universe u

noncomputable section

namespace RingPairCat

variable (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint]

/-- Lemma 15.12.2 (1): the canonical map from a ring pair to its Henselization is flat. -/
@[stacks 0AGU "Lemma 15.12.2 (1)"]
theorem toHenselization_flat : RingHom.Flat (toHenselization X) := sorry

/-- Lemma 15.12.2 (2): the distinguished Henselization ideal is the extension of the source
ideal. -/
@[stacks 0AGU "Lemma 15.12.2 (2)"]
theorem henselizationIdeal_eq_map :
    henselizationIdeal X = Ideal.map (toHenselization X) X.ideal := sorry

/-- The `n`th power of the source ideal maps into the `n`th power of the distinguished
Henselization ideal. -/
theorem ideal_pow_le_comap_toHenselization (n : ℕ) :
    X.ideal ^ n ≤
      Ideal.comap (toHenselization X) ((henselizationIdeal X) ^ n) := sorry

/-- Lemma 15.12.2 (3): reduction modulo every power of the distinguished ideal is unchanged by
pair Henselization. -/
@[stacks 0AGU "Lemma 15.12.2 (3)"]
theorem quotientPowToHenselization_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        (I := X.ideal ^ n) ((henselizationIdeal X) ^ n)
        (toHenselization X) (ideal_pow_le_comap_toHenselization X n)) := sorry

end RingPairCat
