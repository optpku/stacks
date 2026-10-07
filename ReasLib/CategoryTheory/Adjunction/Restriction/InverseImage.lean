module

public import ReasLib.CategoryTheory.Adjunction.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting an adjunction to an inverse-image object property

For `F ⊣ G` and an isomorphism-invariant property `P` on the source of `F`, this leaf
restricts the adjunction between `P` and `P.inverseImage G`.  The unit condition on `P`
and full faithfulness of `G` then give equivalences on both restrictions.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe vC vD uC uD

namespace CategoryTheory.Adjunction.InverseImageRestriction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : ObjectProperty C)

/-- The target property consisting of the objects whose right-adjoint image satisfies `P`. -/
@[stacks 001D "right-adjoint inverse-image property"]
abbrev targetProperty : ObjectProperty D := P.inverseImage G

/-- If the adjunction unit is invertible on `P`, then the left adjoint maps `P` into
`P.inverseImage G`. -/
@[stacks 001D "left adjoint preserves the unit locus"]
theorem left_mapsTo [P.IsClosedUnderIsomorphisms]
    (hunit : P ≤ adj.unitIsoProperty) :
    P ≤ (targetProperty (G := G) P).inverseImage F := sorry

/-- The right adjoint tautologically maps `P.inverseImage G` into `P`. -/
@[stacks 001D "right adjoint preserves its inverse-image property"]
theorem right_mapsTo : targetProperty (G := G) P ≤ P.inverseImage G := sorry

/-- The left adjoint restricted from `P` to `P.inverseImage G`. -/
@[stacks 001D "left inverse-image restriction"]
noncomputable abbrev left [P.IsClosedUnderIsomorphisms]
    (hunit : P ≤ adj.unitIsoProperty) :
    P.FullSubcategory ⥤ (targetProperty (G := G) P).FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict F (left_mapsTo adj P hunit)

/-- The right adjoint restricted from `P.inverseImage G` to `P`. -/
@[stacks 001D "right inverse-image restriction"]
noncomputable abbrev right :
    (targetProperty (G := G) P).FullSubcategory ⥤ P.FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict G (right_mapsTo (G := G) P)

/-- The ambient adjunction restricted between `P` and `P.inverseImage G`. -/
@[stacks 001D "inverse-image restricted adjunction"]
noncomputable abbrev adjunction [P.IsClosedUnderIsomorphisms]
    (hunit : P ≤ adj.unitIsoProperty) :
    left adj P hunit ⊣ right (G := G) P :=
  ObjectProperty.FullSubcategory.adjunction F G adj
    (left_mapsTo adj P hunit) (right_mapsTo (G := G) P)

/-- A fully faithful right adjoint restricts to an equivalence onto `P` when the unit is
invertible on `P`. -/
@[stacks 001D "right inverse-image restriction is an equivalence"]
theorem right_isEquivalence [P.IsClosedUnderIsomorphisms]
    [G.Full] [G.Faithful] (hunit : P ≤ adj.unitIsoProperty) :
    (right (G := G) P).IsEquivalence := sorry

/-- Under the same hypotheses, the restricted left adjoint is the quasi-inverse equivalence. -/
@[stacks 001D "left inverse-image restriction is an equivalence"]
theorem left_isEquivalence [P.IsClosedUnderIsomorphisms]
    [G.Full] [G.Faithful] (hunit : P ≤ adj.unitIsoProperty) :
    (left adj P hunit).IsEquivalence := sorry

/- The underlying functors are concrete restrictions.  Any `sorryAx` below is inherited from
   the Prop-valued membership and adjunction-law statements, not from new object or map data. -/

end CategoryTheory.Adjunction.InverseImageRestriction
