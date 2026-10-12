/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap71.Definition_71_17_1_Blowup
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Algebraic spaces over X with effective Cartier inverse image of a closed subspace

The full subcategory of `Over X` on morphisms whose inverse image of a closed
subspace is an effective Cartier divisor, together with a chosen blowing up as
an object of that subcategory.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Blowup

/-- The full subcategory of `Over X` on morphisms `Y ⟶ X` whose inverse image of
the closed subspace `Z` is an effective Cartier divisor. -/
abbrev effectiveCartierPullbackOverCategory {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :=
  ObjectProperty.FullSubcategory fun Y : Over X ↦ Z.pullbackDefined Y.hom

namespace effectiveCartierPullbackOverCategory

/-- A chosen blowing up of `Z` in `X` has inverse image of `Z` an effective
Cartier divisor, hence is an object of `effectiveCartierPullbackOverCategory Z`. -/
instance instPullbackDefined_along {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) : Z.pullbackDefined π.hom :=
  sorry

/-- A chosen blowing up of `Z` in `X`, as an object of the full subcategory of
`Over X` on which the inverse image of `Z` is an effective Cartier divisor. -/
def blowupObject {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) [h : Z.pullbackDefined π.hom] :
    effectiveCartierPullbackOverCategory Z where
  obj := Over.mk π.hom
  property := h

/-- The underlying object of `blowupObject Z π` is the blowup morphism as an
object of `Over X`. -/
theorem blowupObject_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) [Z.pullbackDefined π.hom] :
    (blowupObject Z π).obj = Over.mk π.hom :=
  sorry

/-- The structure morphism of `blowupObject Z π` is the blowup morphism. -/
theorem blowupObject_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) [Z.pullbackDefined π.hom] :
    (blowupObject Z π).obj.hom = π.hom :=
  sorry

/-- The object `blowupObject Z π` satisfies the defining predicate of
`effectiveCartierPullbackOverCategory Z`. -/
theorem blowupObject_property {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) (π : along Z) [Z.pullbackDefined π.hom] :
    Z.pullbackDefined (blowupObject Z π).obj.hom :=
  sorry

end effectiveCartierPullbackOverCategory

end AlgebraicGeometry.AlgebraicSpace
