module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point.Jacobson
import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
import ReasLib.Topology.Specialization.Dimension.Catenary

/-!
# Relative dimension over Jacobson schemes

This file compares the relative dimension of the generic point of an integral closed subscheme
with its global and closed-stalk Krull dimensions.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- At the generic point of an integral closed subscheme over a Jacobson scheme, the relative
dimension is the integer cast of a natural number. -/
theorem relativeDimensionFunction_generic_eq_natCast
    {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
    [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
    [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
    (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
    (ξ : genericPoints Z.subscheme) :
    f.relativeDimensionFunction δ (Z.subschemeι ξ.1) =
      (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : ℤ) := sorry

/-- The topological Krull dimension of an integral closed subscheme over a Jacobson scheme is
the relative dimension at its generic point. -/
theorem topologicalKrullDim_eq_relativeDimensionFunction_generic
    {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
    [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
    [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
    (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
    (ξ : genericPoints Z.subscheme) :
    topologicalKrullDim Z.subscheme =
      (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : WithBot ℕ∞) := sorry

/-- At every closed point of an integral closed subscheme over a Jacobson scheme, the local ring
has Krull dimension equal to the relative dimension at the generic point. -/
theorem ringKrullDim_stalk_eq_relativeDimensionFunction_generic
    {X S : Scheme.{u}} (f : X ⟶ S) (δ : S → ℤ)
    [UniversallyCatenary S] [JacobsonSpace S] [IsDimensionFunction δ]
    [LocallyOfFiniteType f] (hδ_closed : ∀ s ∈ closedPoints S, δ s = 0)
    (Z : X.IdealSheafData) [AlgebraicGeometry.IsIntegral Z.subscheme]
    (ξ : genericPoints Z.subscheme) (z : Z.subscheme)
    (hz : z ∈ closedPoints Z.subscheme) :
    ringKrullDim ((Z.subscheme).presheaf.stalk z) =
      (Int.toNat (f.relativeDimensionFunction δ (Z.subschemeι ξ.1)) : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Hom
