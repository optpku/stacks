module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter.Finite

open AlgebraicGeometry CategoryTheory

universe u

/- Remark 42.45.1 (1): The Chern-character component `chᵢ(E)` is defined for every
finite locally free module `E`, without requiring its rank to be constant. -/
@[stacks 0ESX] #check
  (AlgebraicGeometry.ChernClass.Theory.characterComponent :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : ChernClass.Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
      TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ p i) ℚ)

/- Remark 42.45.1 (2): The full Chern character is the family of its components in
the completed rational nonnegative Chow-cohomology ring. -/
@[stacks 0ESX] #check
  (AlgebraicGeometry.ChernClass.Theory.character :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      (classes : ChernClass.Theory δ p) (E : X.Modules) [E.IsFiniteLocallyFree],
      ChowCohomology.Nonnegative.RationalCompletion δ p)

/- Remark 42.45.1 (3): For a quasi-compact finite-dimensional scheme, the explicit
finite total Chern character has every component of the completed Chern character. -/
@[stacks 0ESX] #check
  (AlgebraicGeometry.ChernClass.Theory.totalCharacter_component :
    ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      [CompactSpace X] (classes : ChernClass.Theory δ p) (E : X.Modules)
      [E.IsFiniteLocallyFree] (d i : ℕ) (_ : topologicalKrullDim X ≤ d),
      ChowCohomology.Nonnegative.rationalComponent δ p i
          (ChernClass.Theory.totalCharacter δ p classes E d) =
        ChernClass.Theory.character δ p classes E i)
