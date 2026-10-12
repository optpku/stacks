/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Pullback.BaseChange
import StacksCheckRecall

/-!
# Situation 15.7.1: fibre-product base change

The base-change rings, their commutative square, and the induced relative
module functor are owned by `FiberProductBaseChangeSituation`.

@stack 08KK
-/

@[expose] public section

@[stacks 08KK "fiber-product base-change situation"]
#check @FiberProductBaseChangeSituation

-- The three rings in the base-changed diagram.
@[stacks 08KK "first tensor-product base change"]
#check @FiberProductBaseChangeSituation.D

@[stacks 08KK "second tensor-product base change"]
#check @FiberProductBaseChangeSituation.CPrime

@[stacks 08KK "common tensor-product base change"]
#check @FiberProductBaseChangeSituation.C

-- The tensor-product square and its comparison with the pullback.
@[stacks 08KK "commutative tensor-product base-change square"]
#check @FiberProductBaseChangeSituation.tensorSquare

@[stacks 08KK "comparison to the tensor-product pullback"]
#check @FiberProductBaseChangeSituation.tensorPullbackComparison

-- The functor in Situation 15.7.1.
@[stacks 08KK "relative module functor of the tensor square"]
#check @FiberProductBaseChangeSituation.relativeModuleFunctor
