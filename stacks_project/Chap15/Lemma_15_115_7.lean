/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.115.7: tame ramification after adjoining roots of a uniformizer

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.116.7,
tag `0EXW`.

@stack 0EXW
-/

-- The repeated unramified-cover condition in Lemma 15.115.7.
@[stacks 0EXW "unramified uniformizer-root cover"]
#check @DVR.UniformizerRoot.HasUnramifiedCover

-- Lemma 15.115.7, tame ramification via uniformizer-root extensions.
@[stacks 0EXW "Lemma 15.115.7: tame ramification via uniformizer-root extensions"]
#check @DVR.UniformizerRoot.isTamelyRamified_tfae_uniformizerRootCover
