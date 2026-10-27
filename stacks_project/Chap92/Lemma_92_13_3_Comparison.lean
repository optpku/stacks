/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger

/-!
# Comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex
-/

universe u

#check (Algebra.Presentation.LichtenbaumSchlessinger.toComplex :
  ∀ {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Presentation A B ι σ),
    Algebra.cotangentComplex A B ⟶
      Algebra.Presentation.LichtenbaumSchlessinger.complex P)

