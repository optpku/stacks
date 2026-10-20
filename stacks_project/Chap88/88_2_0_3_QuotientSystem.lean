/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.AdicQuotient

/-!
# Adic quotient rings and induced maps

The quotient stages and maps are owned by the shared adic quotient system API.
-/

@[expose] public section

universe u

#check (CommAlgCat.adicQuotientStage :
  ∀ {A : Type u} [CommRing A], (I : Ideal A) →
    (B : Type u) → [CommRing B] → [Algebra A B] → ℕ+ → CommRingCat.{u})

#check (CommAlgCat.adicQuotientMap :
  ∀ {A : Type u} [CommRing A] {B C : Type u}
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C],
    (I : Ideal A) → (B →ₐ[A] C) → (n : ℕ+) →
      B ⧸ (I ^ (n : ℕ)).map (algebraMap A B) →+*
        C ⧸ (I ^ (n : ℕ)).map (algebraMap A C))
