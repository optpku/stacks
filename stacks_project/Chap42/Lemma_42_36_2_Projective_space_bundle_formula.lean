/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.FormulaMap

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 42.36.2 (Projective space bundle formula) -/
@[stacks 02TX] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.formulaMap_bijective :
    ∀ {S X P : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType p]
      (E : X.Modules) (r : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X)
      (hπ : AlgebraicGeometry.Scheme.ProjectiveBundle.Representation π E) (k : ℤ),
      Function.Bijective
        (AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula.formulaMap
          δ p E r π hπ k))
