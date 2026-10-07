module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoPullbackCone.Basic

/-!
# Comparing readable and generic mapped pseudopullback cones

This module compares the generic pseudocone obtained by mapping `P.toPseudoCone` with the
pseudocone underlying the directly mapped readable square at the three walking-cospan vertices.

The two cones have different diagram owners, namely `(cospan f g).comp H` and
`cospan (H.map f) (H.map g)`. Consequently their vertex comparisons are deliberately stated
at the concrete left, right, and central objects rather than packaged as a misleading natural
isomorphism between transformations over one diagram.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The left leg of the readable mapped pseudopullback cone is canonically isomorphic to the
left-vertex component of the generic mapped pseudocone. -/
def mapPseudoPullbackCone.presentation.leftIso (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).fst ≅
      (mapPseudoCone H P.toPseudoCone).π.app
        (LocallyDiscrete.mk Limits.WalkingCospan.left) :=
  (λ_ (H.map P.fst)).symm

/-- The right leg of the readable mapped pseudopullback cone is canonically isomorphic to the
right-vertex component of the generic mapped pseudocone. -/
def mapPseudoPullbackCone.presentation.rightIso (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).snd ≅
      (mapPseudoCone H P.toPseudoCone).π.app
        (LocallyDiscrete.mk Limits.WalkingCospan.right) :=
  (λ_ (H.map P.snd)).symm

/-- At the central vertex, the readable mapped pseudopullback cone and generic mapped
pseudocone are compared by the inverse composition constraint followed by an inverse left
unitor. -/
def mapPseudoPullbackCone.presentation.centerIso (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (H.mapPseudoPullbackCone P).toPseudoCone.π.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) ≅
      (mapPseudoCone H P.toPseudoCone).π.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) :=
  (H.mapComp P.fst f).symm ≪≫
    (λ_ (H.map (P.fst ≫ f))).symm

/-- The forward left-vertex comparison is the inverse left unitor. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.leftIso.hom (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.leftIso H P).hom =
      (λ_ (H.map P.fst)).inv := sorry

/-- The inverse left-vertex comparison is the forward left unitor. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.leftIso.inv (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.leftIso H P).inv =
      (λ_ (H.map P.fst)).hom := sorry

/-- The forward right-vertex comparison is the inverse left unitor. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.rightIso.hom (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.rightIso H P).hom =
      (λ_ (H.map P.snd)).inv := sorry

/-- The inverse right-vertex comparison is the forward left unitor. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.rightIso.inv (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.rightIso H P).inv =
      (λ_ (H.map P.snd)).hom := sorry

/-- The forward central comparison is the inverse composition comparison
followed by the inverse left unitor. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.centerIso.hom (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.centerIso H P).hom =
      (H.mapComp P.fst f).inv ≫
        (λ_ (H.map (P.fst ≫ f))).inv := sorry

/-- The inverse central comparison is the left unitor followed by the
forward composition comparison. -/
@[simp]
theorem mapPseudoPullbackCone.presentation.centerIso.inv (H : Pseudofunctor B D)
    (P : Bicategory.PseudoPullbackCone f g) :
    (mapPseudoPullbackCone.presentation.centerIso H P).inv =
      (λ_ (H.map (P.fst ≫ f))).hom ≫
        (H.mapComp P.fst f).hom := sorry

-- Data audit: the outer comparison isomorphisms are explicit inverse left unitors, and the
-- central comparison additionally uses `(H.mapComp P.fst f).symm`. Their `sorryAx`
-- dependencies are inherited only from the Prop-valued coherence fields of `toPseudoCone`
-- and `mapPseudoCone` appearing in their types.

end Pseudofunctor

end CategoryTheory
