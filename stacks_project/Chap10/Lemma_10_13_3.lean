/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.TensorPower.Insertion
import StacksCheckRecall

/-!
# Generator presentations of symmetric and exterior powers

The slot operations, relation maps, and their fine-grained kernel, exactness,
and surjectivity API are owned by `TensorPower.Insertion`.

@stack 00DP
-/

@[expose] public section

#check @TensorPower.Insertion.SlotPair
#check @TensorPower.Insertion.insert
#check @TensorPower.Insertion.Exterior.relationMap
#check @TensorPower.Insertion.Symmetric.relationMap

@[stacks 00DP "(1), exterior-power generator presentation"]
#check @TensorPower.Insertion.Exterior.generator_exact_sequence

@[stacks 00DP "(2), symmetric-power generator presentation"]
#check @TensorPower.Insertion.Symmetric.generator_exact_sequence
