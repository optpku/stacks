module

public import stacks_project.Chap71.Lemma_71_17_5_Universal_property_blowing_up_OverCategory

/-!
# Lemma 71.17.5

A chosen blowing up of a closed subspace of an algebraic space is a final
object of the full subcategory of spaces over the ambient space on which the
inverse image of the center is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Blowup

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.effectiveCartierPullbackOverCategory

/-- Lemma 71.17.5 (Universal property blowing up): for a scheme `S`, an algebraic
space `X` over `S`, and a closed subspace `Z ⊂ X`, a chosen blowing up
`π : along Z` is a final object of the full subcategory of `Over X` consisting
of morphisms whose inverse image of `Z` is an effective Cartier divisor. -/
@[stacks 085U]
theorem existsUnique_lift {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Z : ClosedSubspace X} (π : along Z) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    (hg : Z.pullbackDefined g) :
    ExistsUnique fun h : Y ⟶ π.space ↦ h ≫ π.hom = g :=
  sorry

/-- Every object of `effectiveCartierPullbackOverCategory Z` admits a unique
morphism to `blowupObject Z π` over `X`. -/
theorem existsUnique_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    (Y : effectiveCartierPullbackOverCategory Z) :
    ExistsUnique fun f : Y ⟶ blowupObject Z π ↦
      f.hom.left ≫ π.hom = Y.obj.hom :=
  sorry

/-- A morphism in `effectiveCartierPullbackOverCategory Z` to the chosen blowup
lies over `X`. -/
theorem hom_w {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z)
    {Y : effectiveCartierPullbackOverCategory Z}
    (f : Y ⟶ blowupObject Z π) :
    f.hom.left ≫ π.hom = Y.obj.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.effectiveCartierPullbackOverCategory
