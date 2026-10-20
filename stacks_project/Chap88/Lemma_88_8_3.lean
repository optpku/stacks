/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.RigSmooth
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 88.8.3: Let `A` be a Noetherian ring and let `I` be an ideal. Let `B`
be an object of (88.2.0.2). If `B` is rig-étale over `(A, I)`, then `B` is
rig-smooth over `(A, I)`. -/
@[stacks 0GB1] #check (Algebra.RigEtale.toRigSmooth :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {B : Type u}
    [CommRing B] [Algebra A B] [Algebra.RigEtale I B], Algebra.RigSmooth I B)
