/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Cohomology
import StacksCheckRecall

@[expose]
public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

/- Lemma 71.15.1: let `R` be a Noetherian ring, let `X` be an algebraic space over
`R` whose structure morphism `f : X ⟶ Spec (CommRingCat.of R)` is proper, and let
`L` be an invertible `𝒪_X`-module. Then `L` is ample on `X/R` in the sense of
`RelativelyAmple f L` if and only if for every coherent `𝒪_X`-module `F` there
exists `n0 ≥ 0` such that `H^p(X, F ⊗ L^{⊗ n}) = 0` for all `n ≥ n0` and all
`p > 0`. -/
@[stacks 0D38] #check
  (AlgebraicGeometry.AlgebraicSpace.relativelyAmple_iff_twist_cohomology_eventually_isZero :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R))))) [Proper f]
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
      (L : X.Modules) [isInvertibleObject L],
      RelativelyAmple f L ↔
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ p, 0 < p →
            IsZero (cohomology X (F ⊗ tensorPower L n) p))
