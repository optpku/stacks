module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition

/-!
# Noether normalization for finite type scheme morphisms

This file provides a relative affine-space factorization whose induced map on
a prescribed fiber is finite.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An affine finite type morphism whose fiber over a point has dimension `d`
factors through relative affine `d`-space so that the induced morphism on that
fiber is finite. -/
theorem exists_affineSpace_factorization_finite_on_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] [FiniteType f]
    (s : S) (d : ℕ) (hfdim : topologicalKrullDim (f.fiber s) = d) :
    ∃ π : X ⟶ AffineSpace (ULift.{u} (Fin d)) S,
      ∃ hπ : π ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = f,
        IsFinite
          ((eqToHom
              (congrArg (fun φ ↦ Scheme.Hom.fiber φ s) hπ.symm)) ≫
            compFiberToBaseFiber π (AffineSpace (ULift.{u} (Fin d)) S ↘ S) s) := sorry

end AlgebraicGeometry.Scheme.Hom
