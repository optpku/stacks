module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Lci
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects

/-!
# Formal smoothness of the LCI Hilbert forgetful morphism

For positive degree, the LCI Hilbert forgetful morphism of a flat, locally
finitely presented morphism of stacks is formally smooth on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom renaming
  Flat → GroupoidFlat, LocallyOfFinitePresentation → GroupoidLocallyOfFinitePresentation,
  FormallySmoothOnObjects → GroupoidFormallySmoothOnObjects
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- For a flat, locally finitely presented morphism of stacks representable by
algebraic spaces, the degree-`d` LCI Hilbert forgetful morphism is formally smooth
on objects when `d` is positive. -/
instance lciForgetToY.formallySmoothOnObjects (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d]
    [GroupoidFlat (asGroupoidsOverMor F)]
    [GroupoidLocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    GroupoidFormallySmoothOnObjects
      (asGroupoidsOverMor (lciForgetToY F d)) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
