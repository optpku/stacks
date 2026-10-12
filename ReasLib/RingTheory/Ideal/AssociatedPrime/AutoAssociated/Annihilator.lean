/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Ideal.AssociatedPrime.AutoAssociated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Annihilators in auto-associated rings

@stack 05GN

The torsion-ideal description of auto-associated rings implies that every proper finitely
generated ideal has nonzero annihilator.
-/

@[expose] public section

open Ideal IsLocalRing

universe u

namespace Ideal

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A torsion ideal of definition forces every proper finitely generated ideal to have nonzero
annihilator. -/
@[stacks 05GN "annihilator criterion from a torsion ideal of definition"]
theorem annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition
    (x : R) (hx : (torsionOf R R x).IsIdealOfDefinition)
    {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := sorry
-- Proof strategy: use locality and `hx` to obtain `I ≤ (torsionOf R R x).radical`, then apply
-- `Ideal.exists_pow_le_of_le_radical_of_fg`.  Choose the least `n` with
-- `I ^ n ≤ torsionOf R R x`; properness gives `n ≠ 0`.  An element of
-- `I ^ (n - 1)` outside the torsion ideal produces a nonzero multiple of `x` annihilated by `I`.

end Ideal

namespace IsAutoAssociatedRing

variable {R : Type u} [CommRing R]

/-- Lemma 15.15.2: every proper finitely generated ideal in an auto-associated ring has nonzero
annihilator. -/
@[stacks 05GN "Lemma 15.15.2"]
theorem annihilator_ne_bot_of_fg_of_ne_top [IsAutoAssociatedRing R]
    {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := sorry
-- Proof strategy: obtain `x` and its torsion ideal of definition from
-- `IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition`, then apply
-- `Ideal.annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition`.

end IsAutoAssociatedRing
