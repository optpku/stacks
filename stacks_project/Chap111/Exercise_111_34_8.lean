/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineLine.FpTAway
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.34.8: for a prime `p`, the localized affine scheme contains a closed
subscheme whose structural morphism to `Spec (Polynomial (ZMod p))` is finite and
surjective. -/
@[stacks 029A] #check
  (AlgebraicGeometry.FpTAwayAffineLine.exists_isClosedImmersion_isFinite_surjective :
    ∀ (p : ℕ) [Fact p.Prime],
      ∃ (Z : Scheme) (i : Z ⟶ AlgebraicGeometry.FpTAwayAffineLine.total p),
        IsClosedImmersion i ∧ IsFinite (i ≫ AlgebraicGeometry.FpTAwayAffineLine.toBase p) ∧
          Surjective (i ≫ AlgebraicGeometry.FpTAwayAffineLine.toBase p))
