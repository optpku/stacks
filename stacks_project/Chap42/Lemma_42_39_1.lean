module

import StacksCheckRecall
public import stacks_project.Chap42.«42_39_1_1»

open CategoryTheory
open scoped BigOperators MonoidalCategory

universe u

/- Lemma 42.39.1: The `i`-th Chern class of a rank-`r` finite locally free module
after tensoring with an invertible module is the corresponding binomial sum in `A⁎(X)`. -/
@[stacks 02UD] #check (AlgebraicGeometry.chernClass_tensor_invertible :
  ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
    [AlgebraicGeometry.LocallyOfFiniteType p]
    (E L : X.Modules) (r i : ℕ)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    [AlgebraicGeometry.Scheme.Modules.Invertible L],
    let hE : E.IsFiniteLocallyFree :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r E
    let hLRank : L.IsFiniteLocallyFreeOfRank 1 :=
      AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible L
    let hL : L.IsFiniteLocallyFree :=
      @AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
        X 1 L hLRank
    let hTensor : (E ⊗ L : X.Modules).IsFiniteLocallyFree :=
      @SheafOfModules.IsFiniteLocallyFree.tensor _ _ _ _ _ _ _ _ _ E L hE hL
    AlgebraicGeometry.ChernClass.homogeneous δ p i
        (@AlgebraicGeometry.ChernClass.chernClass S X inferInstance δ inferInstance
          p inferInstance (E ⊗ L) hTensor i) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j :
          AlgebraicGeometry.ChowCohomology.Nonnegative.ring δ p) *
          AlgebraicGeometry.ChernClass.homogeneous δ p (i - j)
            (@AlgebraicGeometry.ChernClass.chernClass S X inferInstance δ inferInstance
              p inferInstance E hE (i - j)) *
            AlgebraicGeometry.ChernClass.homogeneous δ p 1
              (AlgebraicGeometry.ChowCohomology.firstChernClass δ p L) ^ j)
