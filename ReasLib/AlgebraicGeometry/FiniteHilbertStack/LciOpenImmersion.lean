module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Lci
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Openness of the LCI Hilbert locus

For a flat, locally finitely presented morphism of stacks representable by
algebraic spaces, the inclusion of the degree-`d` LCI Hilbert locus into the
degree-`d` Hilbert stack is a representable open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom renaming
  Flat → GroupoidFlat, LocallyOfFinitePresentation → GroupoidLocallyOfFinitePresentation,
  OpenImmersion → GroupoidOpenImmersion
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

attribute [instance] lciP_isStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- For a flat, locally finitely presented morphism of stacks representable by
algebraic spaces, the inclusion of the degree-`d` LCI Hilbert locus into the
degree-`d` Hilbert stack is a representable open immersion. -/
instance lciInclusion.openImmersion (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [GroupoidFlat (asGroupoidsOverMor F)]
    [GroupoidLocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    GroupoidOpenImmersion (asGroupoidsOverMor (lciInclusion F d)) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
