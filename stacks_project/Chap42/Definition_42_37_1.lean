/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import stacks_project.Chap42.«42_37_1_1»

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Definition 42.37.1: The total Chern class `c(E) ∩ [X]` is the sum of the
homogeneous Chern classes determined by geometric projective-bundle-formula data. -/
@[stacks 02U0] #check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.totalChernClass :
    ∀ {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      [IsIntegral X] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
      (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
      (F : ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn)
      (hF : F.IsGeometric δ p E r π hπ n hn),
      DirectSum ℤ (fun k ↦
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k))

end AlgebraicGeometry
