module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Total
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 42.38.8 (1): For `0 ≤ i ≤ r`, the `i`th Chern class of a rank-`r`
finite locally free module `E` is the degree-`i` bivariant class `ChernClass.FixedRank.component`. -/
@[stacks 0FE1] #check (AlgebraicGeometry.ChernClass.FixedRank.component :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (i : Fin (r + 1)),
    ChowCohomology.degree δ p (i : ℤ))

/- Definition 42.38.8 (2): The total Chern class `c(E)` is the sum of its homogeneous
components `c₀(E), …, cᵣ(E)`, viewed in the nonhomogeneous Chow-cohomology ring. -/
@[stacks 0FE1] #check (AlgebraicGeometry.ChernClass.total :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E], ChowCohomology.ring δ p)

