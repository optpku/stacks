/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.TensorPower.Insertion.Exterior
import StacksCheckRecall

/-!
# Tensor-slot insertion for Lemma 10.13.4

All slot data and insertion operations are owned by
`TensorPower.Insertion`; this file is only the source-facing recall.

@stack 0H1C
-/

@[stacks 0H1C "ordered tensor slots"]
#check @TensorPower.Insertion.SlotPair

@[stacks 0H1C "two-slot insertion"]
#check @TensorPower.Insertion.insert

@[stacks 0H1C "repeated-entry tensor relations"]
#check @TensorPower.Insertion.Exterior.repeatSet

@[stacks 0H1C "linearized repeated-entry relations"]
#check @TensorPower.Insertion.Exterior.repeatMap
