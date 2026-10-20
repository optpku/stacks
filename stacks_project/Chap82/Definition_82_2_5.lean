module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.2.5 (1): In Situation 82.2.1, for any good `X / B` and any
irreducible closed subset `T ⊂ |X|`, the `δ`-dimension of `T` is `δ_{X/B}(ξ)`
where `ξ ∈ T` is the generic point of `T`. -/
@[stacks 0EDX] #check (AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ],
    TopologicalSpace.IrreducibleCloseds (Points X) → ℤ)

/- Definition 82.2.5 (2): If `T ⊂ |X|` is any closed subset, then `dim_δ(T)` is
the supremum of the `δ`-dimensions of the irreducible components of `T`. -/
@[stacks 0EDX] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSetDeltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ],
    TopologicalSpace.Closeds (Points X) → EInt)

/- Definition 82.2.5 (3): If `Z` is a closed subspace of `X`, then
`dim_δ(Z) = dim_δ(|Z|)`. -/
@[stacks 0EDX] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ],
    ClosedSubspace X → EInt)
