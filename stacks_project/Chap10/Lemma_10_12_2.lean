/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IsTensorProduct
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.12.2: Let `M, N` be `R`-modules. Then there exists a pair `(T, g)` where `T` is an
`R`-module and `g` is an `R`-bilinear map with the universal property that every bilinear map
factors uniquely through it; any two such pairs are uniquely isomorphic.

The canonical owner is `IsTensorProduct`: `TensorProduct.isTensorProduct` supplies the universal
property and `IsTensorProduct.equiv` supplies the unique comparison of realizations.

@stack 00CX
-/
@[stacks 00CX "canonical bilinear map"]
#check @TensorProduct.mk

@[stacks 00CX "universal property"]
#check @TensorProduct.isTensorProduct

@[stacks 00CX "uniqueness of realization"]
#check @IsTensorProduct.equiv
