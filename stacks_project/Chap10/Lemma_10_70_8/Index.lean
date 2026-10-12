/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Scaling
import StacksCheckRecall

/-!
# Lemma 10.70.8 index

Compatibility imports for this chapter item resolve directly to the shared
scaling owner.
-/

@[expose] public section

/- Lemma 10.70.8 (0BBI): canonical scaling-map owner. -/
@[stacks 0BBI] #check @AffineBlowupChart.Scaling.map
