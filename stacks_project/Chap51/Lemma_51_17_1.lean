/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Frobenius.Free
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 51.17.1: a finite module over a Noetherian local ring of prime
characteristic is free if its scalar extension along Frobenius is isomorphic to itself. -/
@[stacks 0EBV] #check (Module.free_of_frobeniusBaseChange_iso :
    ∀ (p : ℕ) [Fact p.Prime] {A : Type u} [CommRing A] [IsLocalRing A]
      [IsNoetherianRing A] (hp : (p : A) = 0) (M : ModuleCat.{max u v} A)
      [Module.Finite A M],
      Nonempty ((ModuleCat.extendScalars (RingHom.frobeniusOfPrime p hp)).obj M ≅ M) →
      Module.Free A M)
