/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.QuotientLocalization
import StacksCheckRecall

/-!
# Quotient-localization models

@stack 05N5

The canonical owners are
`Module.Finite.exists_quotient_localized_model` and
`Module.FinitePresentation.exists_quotient_localized_model` in
`ReasLib.Algebra.Module.FinitePresentation.QuotientLocalization`.
The quotient scalar structures are owned by that leaf, so this chapter file
only records the two source clauses.
-/

@[expose] public section

/- Lemma 10.126.3 (1): the finite quotient-localization model is recalled from
the neutral owner `Module.Finite.exists_quotient_localized_model`. -/
@[stacks 05N5 "(1)"]
#check @Module.Finite.exists_quotient_localized_model

/- Lemma 10.126.3 (2): the finitely presented quotient-localization model is
recalled from the neutral owner `Module.FinitePresentation.exists_quotient_localized_model`. -/
@[stacks 05N5 "(2)"]
#check @Module.FinitePresentation.exists_quotient_localized_model
