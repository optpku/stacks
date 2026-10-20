/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u

/- Lemma 61.7.2: if a ring map `A → B` is ind-étale, then for any ring map
`A → A'` the base change `A' → A' ⊗[A] B` is ind-étale.
-/ 
@[stacks 097J] #check (RingHom.IndEtale.baseChange :
  ∀ {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'],
    (algebraMap R A).IndEtale →
      (algebraMap R' (R' ⊗[R] A)).IndEtale)
