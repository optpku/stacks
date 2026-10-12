/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Finite rank decomposition of the flat-in-dimensions functor
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (d : ℕ)
variable [IsAffine X] [IsAffine S] [Smooth f] [GeometricallyIrreducible f]
  [Scheme.Hom.RelativeDimension f d] [ℱ.IsFinitePresentation]

/-- The flat-in-dimensions functor of a finitely presented module on a smooth affine family
with geometrically irreducible fibres of relative dimension `d` is a finite coproduct of its
generic-point rank functors. -/
theorem existsFlatInDimensionsIsoRankCoproduct :
    ∃ c : ℕ,
      Nonempty
        (flatInDimensionsFunctor f ℱ d ≅
          ∐ fun p : Fin (c + 1) ↦ freeAtGenericPointsFunctor f ℱ p) := sorry

end AlgebraicGeometry.Scheme.Flattening
