/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]

#check (Algebra.NaiveCotangent.Adic.naiveCotangent :
    ∀ {A B ι : Type u} [CommRing A] [CommRing B] [Algebra A B] [Fintype ι]
      (I : Ideal A) (P : Presentation A B I ι),
      ChainComplex (ModuleCat B) ℕ)

end Algebra.NaiveCotangent.Adic
