/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.LocallyPreValuationRing
import StacksCheckRecall

/-!
# Lemma 15.125.4 (0ASQ)

@stack 0ASQ

The local-to-global cyclic-retract theorem is owned by the finite-presentation
leaf in ReasLib.  This chapter entry retains only the source label and direct
canonical recall.
-/

@[expose] public section

/- Lemma 15.125.4 (0ASQ): finitely presented modules over a ring whose maximal
localizations are generalized valuation rings are finite cyclic retracts. -/
@[stacks 0ASQ "Lemma 15.125.4, finite cyclic retract over local generalized valuation rings"]
#check
  @Module.FinitePresentation.existsRetractDirectSumPrincipalQuotients_of_localizedPreValuationRing

#print axioms
  Module.FinitePresentation.existsRetractDirectSumPrincipalQuotients_of_localizedPreValuationRing
