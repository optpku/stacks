/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FlatLift.Localization
import StacksCheckRecall

/-!
# Flat algebra lifts versus localization
-/

@[expose] public section

universe u

/- Lemma 93.13.1: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and a multiplicative subset
`S ⊆ B` such that if `Spec(B) ⟶ Spec(A)` is not syntomic at `q` then
`S ∩ q = ∅`, `B` has a flat lift to `A'` if and only if `Localization S`
has a flat lift to `A'`. -/
@[stacks 0DZ7]
#check (Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_localization :
  ∀ {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (S : Submonoid B) (hsyn : (algebraMap A B).SyntomicAtPrimesMeeting S),
    Algebra.NilpotentLift.existsFlatLift A' A B ↔
      Algebra.NilpotentLift.existsFlatLift A' A (Localization S))

end
