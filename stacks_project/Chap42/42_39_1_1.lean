/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Tensor

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum MonoidalCategory

noncomputable section

universe u

/- 42.39.1.1: For a finite locally free module `E` of rank `r` and an invertible
module `L`, the `i`-th Chern class of `E ⊗ L` is the corresponding binomial sum in
`ChowCohomology.Nonnegative.ring δ p`. -/
@[stacks 02UE] #check (AlgebraicGeometry.chernClass_tensor_invertible :
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
