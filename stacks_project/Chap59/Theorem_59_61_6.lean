/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.ConnectingHom
import StacksCheckRecall

@[expose] public section

universe u v

/- Theorem 59.61.6: the matrix-descent connecting map from the Brauer group to continuous
second Galois cohomology with discrete separable-closure units is a group isomorphism. -/
@[stacks 03R7] #check (BrauerGroup.delta_isomorphism :
  ∀ (K : Type u) (Ksep : Type v) [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep], Function.Bijective (BrauerGroup.delta K Ksep))

end
