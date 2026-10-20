module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo

/-!
# Isomorphisms of pseudo comma morphisms

The pseudo comma bicategory is locally full in its colax comma ambient
bicategory.  This leaf therefore lifts an isomorphism of the two endpoint
morphisms whenever its forward cells satisfy the usual comma compatibility.
It is the pseudo-comma counterpart of `ColaxComma.isoMk`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace PseudoComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

/-- The inverse endpoint cells of a compatible pseudo comma isomorphism
satisfy the reverse comma compatibility equation. -/
theorem isoMk_inv_w {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    (F.map₂ left.inv ▷ T.hom) ≫ cell f =
      cell g ≫ (S.hom ◁ G.map₂ right.inv) := sorry

namespace Implementation

/-- The endpoint inverse cells assembled from `PseudoComma.isoMk` cancel on
the source pseudo comma morphism. -/
private theorem isoMk_hom_inv_id {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    hom₂Mk left.hom right.hom w ≫
        hom₂Mk left.inv right.inv (isoMk_inv_w left right w) =
      𝟙 f := sorry

/-- The endpoint inverse cells assembled from `PseudoComma.isoMk` cancel on
the target pseudo comma morphism. -/
private theorem isoMk_inv_hom_id {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    hom₂Mk left.inv right.inv (isoMk_inv_w left right w) ≫
        hom₂Mk left.hom right.hom w =
      𝟙 g := sorry

end Implementation

/-- Construct an isomorphism of pseudo comma morphisms from compatible
isomorphisms of their left and right endpoint maps.

Only the forward comma compatibility is required. The reverse compatibility
and the two inverse laws are derived in the locally full pseudo comma
bicategory. -/
def isoMk {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    f ≅ g where
  hom := hom₂Mk left.hom right.hom w
  inv := hom₂Mk left.inv right.inv (isoMk_inv_w left right w)
  hom_inv_id := Implementation.isoMk_hom_inv_id left right w
  inv_hom_id := Implementation.isoMk_inv_hom_id left right w

/-- The left endpoint cell of the forward morphism in `PseudoComma.isoMk` is
the supplied forward left endpoint cell. -/
@[simp]
theorem isoMk_hom_left₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    left₂ (isoMk left right w).hom = left.hom := sorry

/-- The right endpoint cell of the forward morphism in `PseudoComma.isoMk` is
the supplied forward right endpoint cell. -/
@[simp]
theorem isoMk_hom_right₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    right₂ (isoMk left right w).hom = right.hom := sorry

/-- The left endpoint cell of the inverse morphism in `PseudoComma.isoMk` is
the inverse supplied left endpoint cell. -/
@[simp]
theorem isoMk_inv_left₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    left₂ (isoMk left right w).inv = left.inv := sorry

/-- The right endpoint cell of the inverse morphism in `PseudoComma.isoMk` is
the inverse supplied right endpoint cell. -/
@[simp]
theorem isoMk_inv_right₂ {S T : PseudoComma F G} {f g : S ⟶ T}
    (left : left f ≅ left g) (right : right f ≅ right g)
    (w : (F.map₂ left.hom ▷ T.hom) ≫ cell g =
      cell f ≫ (S.hom ◁ G.map₂ right.hom)) :
    right₂ (isoMk left right w).inv = right.inv := sorry

end PseudoComma

end Bicategory

end CategoryTheory
