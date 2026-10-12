/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Existence
import StacksCheckRecall

/-!
# Dominating Discrete Valuation Subrings

@stack 00PH
-/

@[expose] public section

/- Lemma 10.119.13: a finitely generated field extension of the fraction field
of a non-field Noetherian local domain admits a discrete valuation subring
dominating the image of the base ring. -/
@[stacks 00PH]
#check @ValuationSubring.exists_dvr_dominating_of_not_isField_of_essFiniteType

@[stacks 00PH "finite-dimensional DVR domination"]
#check @ValuationSubring.exists_dvr_dominating_of_not_isField_of_finiteDimensional

end
