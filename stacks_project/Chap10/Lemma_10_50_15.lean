/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.15

@stack 090Q

The canonical owner uses the Bezout-domain formulation; the second recall is
the source-facing finitely-generated-ideal criterion.
-/

/- Lemma 10.50.15 (Tag 090Q): the canonical owner criterion is `ValuationRing.iff_local_bezout_domain`; the
finitely-generated-ideal presentation is the reusable shared bridge. -/
@[stacks 090Q "canonical Bezout-domain criterion"]
#check @ValuationRing.iff_local_bezout_domain

@[stacks 090Q "source finitely-generated-ideal criterion"]
#check @ValuationRing.iff_local_and_fg_ideals_principal
