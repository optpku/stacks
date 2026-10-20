/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Definition_42_38_1_ChernCap
import StacksCheckRecall

/- Definition 42.38.1: Intersection with the `j`th Chern class of a finite locally
free module is the additive operation `c_j(E) ∩ -` on cycles. -/
@[stacks 02U5] #check (AlgebraicGeometry.ChowGroup.ChernCap.operation :
    ∀ {S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ] (X : CategoryTheory.Over S)
      [AlgebraicGeometry.LocallyOfFiniteType X.hom] (E : X.left.Modules) (r : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (F : ∀ (k : ℤ) (x : X.left), X.hom.relativeDimensionFunction δ x = k →
        AlgebraicGeometry.ChowGroup.ChernCap.IntegralFormula δ X E r k x)
      (k : ℤ) (j : Fin (r + 1)),
      AlgebraicGeometry.CycleGroup X.left (X.hom.relativeDimensionFunction δ) k →+
        @AlgebraicGeometry.ChowGroup X.left
          (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance (k - (j : ℕ)))
