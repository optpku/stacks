/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_36_1_ChernPower
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.FormulaMap

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

export Formula
  (formulaTermGrade formulaTerm formulaTerm_apply formulaMap formulaMap_apply
    formulaMap_bijective)

/- The compatibility surface exposes the canonical projective-bundle formula map under the
historical projective-bundle namespace. -/
#check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundle.formulaMap_bijective :
    ∀ {S X P : Scheme.{u}} [UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ),
      Function.Bijective (formulaMap δ p E r π hπ k))

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
