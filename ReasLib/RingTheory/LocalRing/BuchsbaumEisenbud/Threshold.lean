/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.BuchsbaumEisenbud
import Mathlib.Tactic.CrossRefAttribute

/-!
# Threshold for unit rank-minor ideals

For an exact bounded finite-free complex over a Noetherian local ring, the
indices at which the expected rank-minor ideal is the unit ideal form a
terminal interval.

@stack 0GLM
-/

@[expose] public section

universe u

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

/-- Remark 10.102.10: unit rank-minor ideals in an exact bounded finite-free
complex occur precisely from one threshold onward. -/
@[stacks 0GLM]
theorem rankMinorIdeal_eq_top_iff_ge_threshold
    (C : _root_.FiniteFreeComplex R e) (hExact : C.ExactInPositiveDegrees) :
    ∃ j : Fin (e + 1), ∀ i : Fin e, I(C.diffAt i) = ⊤ ↔ j ≤ i.castSucc := sorry

end FiniteFreeComplex
