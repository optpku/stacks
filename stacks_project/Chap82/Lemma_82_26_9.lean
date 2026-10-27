/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowCohomology.Vanishing

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 82.26.9 -/
@[stacks 0ERS] #check
  (AlgebraicGeometry.AlgebraicSpace.OperationalChow.eq_zero_iff_cap_fundamental :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S},
      [UniversallyCatenary B] → [IsQuasiSeparated B] →
      (f : X ⟶ B) → [QuasiSeparated f] → [LocallyOfFiniteType f] →
      (δ : Points B → ℤ) → [IsDimensionFunction δ] → (p : ℤ) →
      (c : AlgebraicGeometry.AlgebraicSpace.OperationalChow δ f p) →
      c = AlgebraicGeometry.AlgebraicSpace.OperationalChow.zero δ f p ↔
        ∀ (Y : AlgebraicSpace S) (g : Y ⟶ X),
          [QuasiSeparated (g ≫ f)] → [LocallyOfFiniteType (g ≫ f)] →
          [LocallyOfFiniteType g] → [IsIntegral Y] →
          AlgebraicGeometry.AlgebraicSpace.OperationalChow.cap_fundamental δ f c g = 0)
