module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClass

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry

/- 42.37.3.1: For the dual tautological module `𝒪_P(-1)` on the projective bundle,
the unsigned sum `∑ i, c₁(𝒪_P(-1)) ^ i ∩ π ^* c_(r-i)` vanishes in
`CH_(n-1)(P)`. -/
@[stacks 05M8] #check
  (AlgebraicGeometry.chernClass_projectiveBundle_dual_relation :
    ∀ {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      [IsIntegral X] (E : X.Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
      [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
      (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
      (F : ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn)
      (hF : ∀ j, F.pullbackThenC1PowerCap j =
        ChowGroup.ProjectiveBundle.Formula.chernTerm δ p E r π hπ n j),
      ∑ i : Fin (r + 1),
          F.dualC1PowerCap δ p E r π hπ n hn i.rev
            (F.chernClass δ p E r π hπ n hn i.rev) =
        0)

end AlgebraicGeometry
