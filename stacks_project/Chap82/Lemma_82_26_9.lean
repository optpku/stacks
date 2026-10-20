/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Lemma_82_26_9_Chow
public import stacks_project.Chap82.Lemma_82_26_9_Operational

/-!
# Vanishing of operational classes on good algebraic spaces

In Situation 82.2.1, a class in `A^p(X)` vanishes if and only if it caps to
zero on the fundamental class of every integral algebraic space locally of
finite type over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowCohomology

/-- Lemma 82.26.9: In Situation 82.2.1 let `X / B` be good. Let `c` be a class
in `A^p(X)`. Then `c` is zero if and only if `c ∩ [Y] = 0` in `CH_*(Y)` for
every integral algebraic space `Y` locally of finite type over `X`. -/
@[stacks 0ERS]
theorem vanishes_iff_cap_fundamental {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (p : ℤ) (c : degree δ f p) :
    Vanishes c ↔
      ∀ (Y : AlgebraicSpace S) (g : Y ⟶ X)
        [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
        [LocallyOfFiniteType g] [IsIntegral Y],
        cap_fundamental c g = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ChowCohomology
