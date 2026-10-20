/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Jacobian

universe u

#check (Algebra.NaiveCotangent.Adic.Presentation.jacobianMinor :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {I : Ideal A} {ι : Type u}
    (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι) {m : ℕ}
    (fs : Fin m → P.ker) (cols : Fin m ↪ ι), B)
