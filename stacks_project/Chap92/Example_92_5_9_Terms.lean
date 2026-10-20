/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LengthTwo.Terms

/-!
# Polynomial terms through degree two

The shared owner provides the explicit polynomial terms and generator maps.
This entry also preserves their exports for the length-two tensor construction.
-/

@[expose] public section

universe u

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

#check (Algebra.Presentation.LengthTwo.Rel :
  (P : Algebra.Presentation A B ι σ) → Submodule P.Ring (σ →₀ P.Ring))

#check (Algebra.Presentation.LengthTwo.faceZero :
  (P : Algebra.Presentation A B ι σ) → Algebra.Presentation.LengthTwo.term1 P →ₐ[A] P.Ring)

#check (Algebra.Presentation.LengthTwo.faceOne :
  (P : Algebra.Presentation A B ι σ) → Algebra.Presentation.LengthTwo.term1 P →ₐ[A] P.Ring)

#check (Algebra.Presentation.LengthTwo.faceTwo :
  (P : Algebra.Presentation A B ι σ) → Fin 3 →
    Algebra.Presentation.LengthTwo.term2 P →ₐ[A] Algebra.Presentation.LengthTwo.term1 P)

#check (Algebra.Presentation.LengthTwo.degeneracyOne :
  (P : Algebra.Presentation A B ι σ) → Fin 2 →
    Algebra.Presentation.LengthTwo.term1 P →ₐ[A] Algebra.Presentation.LengthTwo.term2 P)
