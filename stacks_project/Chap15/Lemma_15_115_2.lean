/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
import StacksCheckRecall

/-!
# Lemma 15.115.2: adjoining a root of a uniformizer

The concrete root ring and fraction-field extension, their ramification
properties, and the intermediate-field classification are owned by
`DVR.UniformizerRoot`.

The repository path retains the legacy chapter numbering; the current Stacks entry is
Lemma 15.116.2.

@stack 09EV
-/

@[expose] public section

-- The explicit polynomial, quotient rings, and distinguished root.
@[stacks 09EV "uniformizer-root model"]
#check @DVR.UniformizerRoot.polynomial
@[stacks 09EV "uniformizer-root extension ring"]
#check @DVR.UniformizerRoot.RootRing
@[stacks 09EV "uniformizer-root fraction polynomial"]
#check @DVR.UniformizerRoot.fractionPolynomial
@[stacks 09EV "uniformizer-root field extension"]
#check @DVR.UniformizerRoot.RootExtension
@[stacks 09EV "distinguished uniformizer root"]
#check @DVR.UniformizerRoot.root
@[stacks 09EV "distinguished uniformizer-root equation"]
#check @DVR.UniformizerRoot.root_pow

-- Lemma 15.115.2 (1), degree of the root extension.
@[stacks 09EV "(1) degree of the uniformizer-root extension"]
#check @DVR.UniformizerRoot.finrank_eq

-- Lemma 15.115.2 (2), identification of the integral closure.
@[stacks 09EV "(2) uniformizer-root integral closure"]
#check @DVR.UniformizerRoot.rootRing_isIntegralClosure

-- Lemma 15.115.2 (3), the DVR property of the root ring.
@[stacks 09EV "(3) uniformizer-root ring is a DVR"]
#check @DVR.UniformizerRoot.rootRing_isDVR

-- Lemma 15.115.2 (4), the ramification index.
@[stacks 09EV "(4) uniformizer-root ramification index"]
#check @DVR.UniformizerRoot.ramificationIndex_eq

-- Lemma 15.115.2 (5), total ramification.
@[stacks 09EV "(5) total ramification of the uniformizer-root extension"]
#check @DVR.UniformizerRoot.isTotallyRamified

-- Lemma 15.115.2 (6a), tame ramification under the prime-to-characteristic condition.
@[stacks 09EV "(6a) tame ramification of the uniformizer-root extension"]
#check @DVR.UniformizerRoot.isTamelyRamified

-- Lemma 15.115.2 (6b), the intermediate-field classification.
@[stacks 09EV "(6b) intermediate fields of a tame uniformizer-root extension"]
#check @DVR.UniformizerRoot.exists_eq_adjoin_root_pow
