/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FlatLift.AdicCompletion
import StacksCheckRecall

/-!
# Flat algebra lifts versus adic completion
-/

@[expose] public section

universe u

/- Lemma 93.12.3: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and an ideal `b ⊆ B` such that
`Spec(B) ⟶ Spec(A)` is syntomic on the complement of `V(b)`, `B` has a flat
lift to `A'` if and only if the `b`-adic completion `AdicCompletion b B` has a
flat lift to `A'`. -/
@[stacks 0DZ3]
#check (Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_adicCompletion :
  ∀ {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b),
    Algebra.NilpotentLift.existsFlatLift A' A B ↔
      Algebra.NilpotentLift.existsFlatLift A' A (AdicCompletion b B))

end
