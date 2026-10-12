/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Reduced
import StacksCheckRecall

/-!
# Lemma 10.70.9 recall

@stack 052S

Reducedness of affine blowup charts is a reusable instance owned by ReasLib.
-/

@[expose] public section

/- Lemma 10.70.9 (052S): every affine chart of a blowup of a reduced ring is
reduced. -/
@[stacks 052S] #check @AffineBlowupChart.instIsReduced
