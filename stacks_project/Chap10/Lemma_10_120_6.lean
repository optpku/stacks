/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.UFD
import StacksCheckRecall

/-!
# Height-one prime ideals and unique factorization

@stack 0AFT
-/

@[expose] public section

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/- Lemma 10.120.6 (Stacks tag `0AFT`): a Noetherian domain is a unique
factorization domain if and only if every height-one prime ideal is principal.
The canonical owner is Mathlib's `UniqueFactorizationMonoid` criterion. -/
@[stacks 0AFT]
#check @UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one

@[stacks 0AFT "height-one principal ideal projection"]
#check @UniqueFactorizationMonoid.isPrincipal_of_height_eq_one

@[stacks 0AFT "height-one principal ideal construction"]
#check @UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
