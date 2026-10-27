/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Valuation.Characterization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.50.15

@stack 090Q

The canonical owner uses the Bezout-domain formulation.  The defining field
`IsBezout.isPrincipal_of_FG` is precisely the source's condition that every
finitely generated ideal is principal.
-/

/- Lemma 10.50.15 (Tag 090Q): a domain is a valuation ring iff it is local and Bezout. -/
@[stacks 090Q "canonical Bezout-domain criterion"]
#check @ValuationRing.iff_local_bezout_domain

@[stacks 090Q "source finitely-generated-ideal criterion"]
#check @IsBezout.isPrincipal_of_FG
