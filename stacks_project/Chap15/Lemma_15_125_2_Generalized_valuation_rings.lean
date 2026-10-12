/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Generalized
import StacksCheckRecall

/-!
# Lemma 15.125.2 (Generalized valuation rings)

@stack 0ASN

The three source formulations are owned by the valuation-ring leaf; this file
records only the labeled recall and the canonical `PreValuationRing` bridge.
-/

@[expose] public section

@[stacks 0ASN "Lemma 15.125.2 (Generalized valuation rings), TFAE"]
#check @ValuationRing.generalizedValuationRing_tfae

@[stacks 0ASN "canonical divisibility formulation"]
#check @PreValuationRing.iff_dvd_total

#print axioms ValuationRing.generalizedValuationRing_tfae
