/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FormalSmooth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.5

The source equivalence is kept as the source-facing statement, while its two predicates are owned
by the reusable DVR-extension and adic-smoothness modules.  The repository path retains the legacy
`15.112.5` name; tag `09E7` is the current Stacks `15.113.5` entry.

@stack 09E7
-/

/- Lemma 15.112.5 (09E7; current Stacks Lemma 15.113.5): the source-facing equivalence is owned
by the reusable extension leaf. -/
@[stacks 09E7 "formal smoothness and weak unramifiedness"]
#check @formally_smooth_for_maximalIdeal_adic_iff_weakly_unramified_and_separable_residueField
