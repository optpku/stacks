/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

/- Lemma 55.3.3: the rational genus expression associated to a numerical type
is the cast of an integer. -/
@[stacks 0C71] #check (NumericalType.genusExpression_isInteger : ∀ (T : NumericalType),
    ∃ g : ℤ, (g : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2))
