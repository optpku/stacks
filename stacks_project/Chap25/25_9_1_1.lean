/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Coskeleton
import StacksCheckRecall

/-! # The endpoint-pair coskeleton square -/

/- Equation 25.9.1.1 (01GQ) is the degree `n + 1` specialization of the naturality square
for the coskeleton unit at the canonical endpoint-pair map. -/
@[stacks 01GQ] #check
  @CategoryTheory.SimplicialObject.internalHom.deltaOne.endpointPair.coskUnitSq

#check @CategoryTheory.SimplicialObject.internalHom.deltaOne.endpointPair
#check @CategoryTheory.SimplicialObject.internalHom.deltaOne.endpointPair.fst
#check @CategoryTheory.SimplicialObject.internalHom.deltaOne.endpointPair.snd
