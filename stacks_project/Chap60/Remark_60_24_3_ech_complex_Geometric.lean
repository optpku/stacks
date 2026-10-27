/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Geometry
public import ReasLib.CategoryTheory.Pro.Presentation

@[expose] public section

universe u

open CategoryTheory

/- Completed geometric stage maps descend along the specified ring homomorphism. -/
#check (CechCrisCover.adicStageMap :
  {B D : Type u} → [CommRing B] → [CommRing D] →
    (p : ℕ) → (B →+* D) → {n m : ℕ} → m ≤ n →
      (B ⧸ Ideal.span ({(p : B)} : Set B) ^ n) →+*
        (D ⧸ Ideal.span ({(p : D)} : Set D) ^ m))
