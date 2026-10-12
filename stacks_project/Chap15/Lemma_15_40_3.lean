/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Flat
import StacksCheckRecall

/-!
# Lemma 15.40.3 (07NP)

@stack 07NP
-/

@[expose] public section

/- Lemma 15.40.3 (07NP), recalled from the canonical adic-smoothness owner. -/
@[stacks 07NP] #check @RingHom.flat_of_formallySmooth_for_maximalIdeal_adic
