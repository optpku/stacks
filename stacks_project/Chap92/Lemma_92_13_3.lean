/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger
import StacksCheckRecall

/-!
# Comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex

Lemma 92.13.3 records the canonical cochain map `L_{B/A} ⟶ L` of a polynomial
presentation, identifying the Lichtenbaum–Schlessinger complex with the good
truncation `τ_{≥ -2} L_{B/A}`.
-/

universe u

/- Lemma 92.13.3. -/
@[stacks 09CG] #check (Algebra.Presentation.LichtenbaumSchlessinger.toComplex_truncGE_quasiIso :
  ∀ {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Presentation A B ι σ),
    QuasiIso (CochainComplex.truncGEMap
      (Algebra.Presentation.LichtenbaumSchlessinger.toComplex P) (-2)))

#check (Algebra.Presentation.LichtenbaumSchlessinger.toComplex :
  ∀ {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Presentation A B ι σ),
    Algebra.cotangentComplex A B ⟶
      Algebra.Presentation.LichtenbaumSchlessinger.complex P)
