module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.Jacobson
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 82.2.4. Over a Jacobson base whose dimension function vanishes on closed points,
the relative dimension at the generic point of an integral closed subspace agrees with its
topological dimension and its closed-point codimensions and local-ring dimensions. -/
@[stacks 0EDW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction_generic_eq_natCast :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))),
    AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : ℤ))

@[stacks 0EDW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.topologicalKrullDim_eq_relativeDimensionFunction_generic :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))),
    topologicalKrullDim (Points Z.X) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞))

@[stacks 0EDW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.coheight_closedPoint_eq_relativeDimensionFunction_generic :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)),
    (Order.coheight (toIrreducibleCloseds z) : WithBot ℕ∞) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞))

@[stacks 0EDW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.localRingDimAt_eq_relativeDimensionFunction_generic :
    ∀ {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)),
    localRingDimAt z =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞))

@[stacks 0EDW] #check (AlgebraicGeometry.AlgebraicSpace.Hom.ringKrullDim_etaleLocalRing_eq_relativeDimensionFunction_generic :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f]
    [LocallyOfFiniteType f] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X))
    (zbar : GeometricPoint Z.X) (hzbar : zbar.liesOver z),
    ringKrullDim (etaleLocalRing Z.X zbar) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞))
