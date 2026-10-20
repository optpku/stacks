module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.RelativeFunction
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic

/-!
# Relative dimension of integral closed subspaces over Jacobson bases

In the good setup over a Jacobson universally catenary base whose dimension
function vanishes on closed points, the relative dimension at the generic
point of an integral closed subspace equals the topological, codimension,
local-ring, and étale-local-ring dimensions of that subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Over a universally catenary Jacobson base with a dimension function vanishing on closed
points, the relative dimension at the generic point of an integral closed subspace of a
quasi-separated locally finite-type algebraic space is the integer cast of its natural part. -/
@[stacks 0EDW]
theorem relativeDimensionFunction_generic_eq_natCast {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))) :
    AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : ℤ) :=
  sorry

/-- Over a universally catenary Jacobson base with a dimension function vanishing on closed
points, the topological Krull dimension of an integral closed subspace of a quasi-separated
locally finite-type algebraic space equals the relative dimension at its generic point. -/
@[stacks 0EDW]
theorem topologicalKrullDim_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))) :
    topologicalKrullDim (Points Z.X) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Over a universally catenary Jacobson base with a dimension function vanishing on closed
points, the coheight of every closed point of an integral closed subspace of a quasi-separated
locally finite-type algebraic space equals the relative dimension at its generic point. -/
@[stacks 0EDW]
theorem coheight_closedPoint_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)) :
    (Order.coheight (toIrreducibleCloseds z) : WithBot ℕ∞) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Over a universally catenary Jacobson base with a dimension function vanishing on closed
points, the local-ring dimension at every closed point of an integral closed subspace of a
quasi-separated locally finite-type algebraic space equals the relative dimension at its
generic point. -/
@[stacks 0EDW]
theorem localRingDimAt_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)) :
    localRingDimAt z =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Over a universally catenary Jacobson base with a dimension function vanishing on closed
points, the étale-local-ring dimension at every geometric point above a closed point of an
integral closed subspace of a quasi-separated locally finite-type algebraic space equals the
relative dimension at its generic point. -/
@[stacks 0EDW]
theorem ringKrullDim_etaleLocalRing_eq_relativeDimensionFunction_generic
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f]
    [LocallyOfFiniteType f] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X))
    (zbar : GeometricPoint Z.X) (hzbar : zbar.liesOver z) :
    ringKrullDim (etaleLocalRing Z.X zbar) =
      (Int.toNat (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDimensionFunction f δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
