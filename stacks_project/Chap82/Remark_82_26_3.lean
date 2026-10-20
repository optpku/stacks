/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import stacks_project.Chap82.Remark_82_26_3_Pullback

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Remark 82.26.3: in Situation 82.2.1, a morphism `f : X ⟶ Y` of good
algebraic spaces over `B` induces a canonical `ℤ`-algebra map `A⁎(Y) → A⁎(X)`.
For `c ∈ A^p(Y)` and a test `X' ⟶ X`, the class `f⁎ c` acts by `c ∩ -` after
viewing `X'` as an algebraic space over `Y` via `X' ⟶ X ⟶ Y`. -/
@[stacks 0ERL] #check (@AlgebraicGeometry.AlgebraicSpace.ChowCohomology.restrict :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    {X Y : AlgebraicSpace S} (pY : Y ⟶ B) (f : X ⟶ Y)
    [QuasiSeparated pY] [LocallyOfFiniteType pY]
    [QuasiSeparated (f ≫ pY)] [LocallyOfFiniteType (f ≫ pY)],
    AlgebraicGeometry.AlgebraicSpace.ChowCohomology.ring δ pY →ₐ[ℤ]
      AlgebraicGeometry.AlgebraicSpace.ChowCohomology.ring δ (f ≫ pY))
