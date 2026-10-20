module

import StacksCheckRecall
public import stacks_project.Chap82.Lemma_82_28_1_Chern
public import stacks_project.Chap82.Definition_82_28_2_Total

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open scoped BigOperators

universe u

/- Definition 82.28.2 (1): In Situation 82.2.1 let `X / B` be good. Let `E`
be a finite locally free `𝒪_X`-module of rank `r = q + 1`. For
`i = 0, …, r` the `i`th Chern class of `E` is the bivariant class
`c_i(E) ∈ A^i(X)` of degree `i` constructed in Lemma 82.28.1. -/
@[stacks 0ERZ] #check
  (ConstantRankChern.degree :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (i : ℕ) (hi : i ≤ q + 1),
      ChowCohomology.degree δ f i)

/- Definition 82.28.2 (2): The total Chern class of `E` is the formal sum
`c(E) = c_0(E) + … + c_r(E)`, viewed as a nonhomogeneous bivariant class
on `X`. -/
@[stacks 0ERZ] #check
  (ConstantRankChern.total :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E],
      ChowCohomology.ring δ f)
