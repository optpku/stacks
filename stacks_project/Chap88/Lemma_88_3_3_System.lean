/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.InverseSystem

/-!
# Stage naive cotangent complexes

The stage complex is owned by the adic naive cotangent inverse-system API.
-/

@[expose] public section

universe u

/- Lemma 88.3.3: the polynomial Jacobian complex at each positive adic stage. -/
#check (Algebra.NaiveCotangent.Adic.stageComplex :
  ∀ {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B],
    (I : Ideal A) → Algebra.NaiveCotangent.Adic.Presentation A B I ι →
      [Fintype ι] → (n : ℕ) →
        ChainComplex (ModuleCat (B ⧸ Algebra.NaiveCotangent.Adic.stageIdeal I n)) ℕ)
