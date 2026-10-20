/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.EulerSequence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/-
Lemma 50.11.1: if `A` is a commutative ring and `1 ≤ n`, then the cotangent sheaf of
standard projective `n`-space over `A`, `n + 1` copies of `𝒪(-1)`, and the structure sheaf
form a short exact sequence
`0 ⟶ Ω ⟶ 𝒪(-1) ^ (n + 1) ⟶ 𝒪 ⟶ 0`.
-/
@[stacks 0FMH] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_eulerSequence_shortExact :
    ∀ (A : Type u) [CommRing A] (n : ℕ), 1 ≤ n →
      ∃ (ι : Ω[(ProjectiveSpace.toSpec A n).toShHom] ⟶
          ∐ fun _ : Fin (n + 1) ↦ ProjectiveSpace.twistingSheaf A n (-1))
        (π : (∐ fun _ : Fin (n + 1) ↦ ProjectiveSpace.twistingSheaf A n (-1)) ⟶
          (SheafOfModules.unit (ProjectiveSpace.scheme A n).ringCatSheaf :
            (ProjectiveSpace.scheme A n).Modules))
        (hιπ : ι ≫ π = 0),
        (ShortComplex.mk ι π hιπ).ShortExact)
