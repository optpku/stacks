module

public import ReasLib.CategoryTheory.Pro.Sequential.Quotient.Functoriality
public import ReasLib.CategoryTheory.Pro.Sequential.Shift

/-!
# Sequential pro-morphism classes from natural transformations

A natural transformation of inverse sequences determines a canonical common-refinement class.
Its comparison with actual pro-morphisms is exactly `Pro.lim.map`, and it is compatible with
identities, composition, and functorial postcomposition.
-/

@[expose] public section

open CategoryTheory

universe u v uD vD

namespace CategoryTheory.Pro.SequentialHom.Quotient

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}

/-- The common-refinement class represented by a natural transformation of inverse sequences. -/
def ofNatTrans (α : X ⟶ Y) : Pro.SequentialHom.Quotient (X := X) (Y := Y) :=
  _root_.Quotient.mk (setoid (X := X) (Y := Y))
    (Pro.SequentialHom.ofNatTrans α)

/-- The pro-morphism associated to `ofNatTrans α` is the image of `α` under the canonical
sequential presentation functor. -/
@[simp]
theorem quotientToHom_ofNatTrans (α : X ⟶ Y) :
    quotientToHom (ofNatTrans α) = (Pro.lim (C := C) ℕᵒᵖ).map α := sorry

/-- The identity natural transformation determines the identity common-refinement class. -/
@[simp]
theorem ofNatTrans_id (X : SequentialInverseSystem C) :
    ofNatTrans (𝟙 X) = id X := sorry

/-- Vertical composition of natural transformations determines composition of their classes. -/
@[simp]
theorem ofNatTrans_comp {Z : SequentialInverseSystem C} (α : X ⟶ Y) (β : Y ⟶ Z) :
    ofNatTrans (α ≫ β) = comp (ofNatTrans α) (ofNatTrans β) := sorry

/-- Postcomposition of a natural-transformation class is the class of the whiskered natural
transformation. -/
@[simp]
theorem map_ofNatTrans {D : Type uD} [Category.{vD} D]
    (α : X ⟶ Y) (F : C ⥤ D) :
    map (ofNatTrans α) F = ofNatTrans (Functor.whiskerRight α F) := sorry

end CategoryTheory.Pro.SequentialHom.Quotient
