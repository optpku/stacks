/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.IntegralClosure.QuotientDecomposition
import StacksCheckRecall

/-!
# Quotient decompositions of integral closures

The reusable quotient comparison and decomposition statement are owned by `ReasLib`.  This file
records the source label without rebuilding the idempotent and localization infrastructure inside
the chapter.

@stack 09XH
-/

@[expose] public section

#check @integralClosure.quotientMap

/- Lemma 15.11.5: a finite component of `B ⧸ I B` lifts to a compatible component of the
reduction of `integralClosure A B`, selected by an element whose away map is an isomorphism. -/
@[stacks 09XH]
#check @exists_integralClosure_product_decomposition_mod_ideal_with_localization
