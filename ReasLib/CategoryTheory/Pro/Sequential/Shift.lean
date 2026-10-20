module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Functoriality
public import ReasLib.CategoryTheory.Pro.Sequential.Realization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shift and natural-transformation representatives of sequential pro-morphisms

@stack 0G2W

This leaf supplies canonical monotone representatives associated to maps of sequential inverse
systems.  The public API uses `Pro.SequentialHom` directly; it does not retain the former
chapter-local representative spelling.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v uB vB

namespace CategoryTheory

namespace Pro.SequentialHom

variable {A : Type u} [Category.{v} A] {X Y : SequentialInverseSystem A}

/-- Build a sequential pro-morphism representative from a natural transformation out of the
source inverse system shifted by `c`. -/
def ofShiftNatTrans (c : ℕ) (α : X.shift c ⟶ Y) :
    Pro.SequentialHom X Y where
  reindex :=
    { toFun := fun n ↦ c + n
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h c }
  hom := α

/-- The reindexing of `ofShiftNatTrans c α` sends `n` to `c + n`. -/
@[simp]
theorem ofShiftNatTrans_reindex_apply (c : ℕ) (α : X.shift c ⟶ Y) (n : ℕ) :
    (ofShiftNatTrans c α).reindex n = c + n := sorry

/-- The level map of `ofShiftNatTrans c α` is the corresponding component of `α`. -/
@[simp]
theorem ofShiftNatTrans_hom_app (c : ℕ) (α : X.shift c ⟶ Y) (n : ℕᵒᵖ) :
    (ofShiftNatTrans c α).hom.app n = α.app n := sorry

/-- The level maps of `ofShiftNatTrans c α` satisfy the naturality square of `α`. -/
@[reassoc]
theorem ofShiftNatTrans_naturality (c : ℕ) (α : X.shift c ⟶ Y)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((ofShiftNatTrans c α).reindex.toFunctor.op ⋙ X).map f ≫
        (ofShiftNatTrans c α).hom.app j =
      (ofShiftNatTrans c α).hom.app i ≫ Y.map f := sorry

/-- The sequential representative induced by a natural transformation of inverse systems. -/
def ofNatTrans (α : X ⟶ Y) : Pro.SequentialHom X Y where
  reindex := OrderHom.id
  hom := α

/-- The reindexing of a natural-transformation representative is the identity. -/
@[simp]
theorem ofNatTrans_reindex (α : X ⟶ Y) :
    (ofNatTrans α).reindex = OrderHom.id := sorry

/-- The level map of a natural-transformation representative is the original component. -/
theorem ofNatTrans_hom_app (α : X ⟶ Y) (n : ℕᵒᵖ) :
    (ofNatTrans α).hom.app n = α.app n := sorry

/-- The sequential representative of the identity natural transformation is the identity
representative. -/
@[simp]
theorem ofNatTrans_id (X : SequentialInverseSystem A) :
    ofNatTrans (𝟙 X) = id X := sorry

/-- Sequential representatives of natural transformations respect composition. -/
@[simp]
theorem comp_ofNatTrans {Z : SequentialInverseSystem A} (α : X ⟶ Y) (β : Y ⟶ Z) :
    comp (ofNatTrans α) (ofNatTrans β) = ofNatTrans (α ≫ β) := sorry

/-- The pro-morphism represented by a natural transformation is the image of that natural
transformation under the canonical sequential presentation functor. -/
@[simp]
theorem toHom_ofNatTrans (α : X ⟶ Y) :
    (ofNatTrans α).toHom = (Pro.lim (C := A) ℕᵒᵖ).map α := sorry

/-- Postcomposing the representative of a natural transformation is the representative of its
whiskering on the right. -/
@[simp, stacks 0G2W "functorial natural-transformation representative"]
theorem map_ofNatTrans {B : Type uB} [Category.{vB} B] (α : X ⟶ Y) (F : A ⥤ B) :
    (ofNatTrans α).map F = ofNatTrans (Functor.whiskerRight α F) := sorry

/-- Realizing a stagewise image of a natural-transformation representative gives the morphism
induced by the whiskered natural transformation between the corresponding pro-objects. -/
@[simp, stacks 0G2W "functorial natural-transformation realization"]
theorem toHom_map_ofNatTrans {B : Type uB} [Category.{vB} B]
    (α : X ⟶ Y) (F : A ⥤ B) :
    ((ofNatTrans α).map F).toHom =
      (Pro.lim (C := B) ℕᵒᵖ).map (Functor.whiskerRight α F) := sorry

/-- Convert a natural transformation indexed by `OrderDual ℕ` into the canonical sequential
inverse-system presentation. -/
def ofOrderDualNatTrans {X Y : OrderDual ℕ ⥤ A} (α : X ⟶ Y) :
    Pro.SequentialHom
      ((orderDualEquivalence ℕ).inverse ⋙ X)
      ((orderDualEquivalence ℕ).inverse ⋙ Y) :=
  ofNatTrans (Functor.whiskerLeft (orderDualEquivalence ℕ).inverse α)

/-- The level map of an order-dual natural-transformation representative is induced by
whiskering the original transformation along the canonical equivalence. -/
theorem ofOrderDualNatTrans_hom_app {X Y : OrderDual ℕ ⥤ A} (α : X ⟶ Y) (n : ℕᵒᵖ) :
    (ofOrderDualNatTrans α).hom.app n =
      (Functor.whiskerLeft (orderDualEquivalence ℕ).inverse α).app n := sorry

end Pro.SequentialHom

end CategoryTheory
