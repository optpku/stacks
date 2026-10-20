/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.FullyFaithful
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing
open CategoryTheory

universe u

/- Lemma 81.11.3: In Situation 81.10.6 the functor (81.11.0.1) is fully
faithful on algebraic spaces separated over `X`. More precisely, it induces a
bijection `Mor_X(X'_1, X'_2) ⟶ Mor_{category f i}(F(X'_1), F(X'_2))` whenever
`X'_2 → X` is separated. -/
@[stacks 0AF6] #check
  (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor_map_bijective :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i] {X₁ X₂ : Over X} [Separated X₂.hom],
      Function.Bijective
        ((AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor f i).map :
          (X₁ ⟶ X₂) → ((AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor f i).obj X₁ ⟶ (AlgebraicGeometry.AlgebraicSpace.FormalGlueing.functor f i).obj X₂)))
