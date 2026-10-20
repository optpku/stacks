module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural transformations between full-subcategory lifts

A natural transformation between ambient functors lifts canonically when
both functors take values in the same full subcategory.  This file supplies
the 2-cell counterpart of `ObjectProperty.lift` and its basic computation and
functoriality laws.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (P : ObjectProperty D)

/-- Naturality of the componentwise lift of an ambient natural
transformation to a full subcategory. -/
theorem liftNatTrans_naturality
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    (P.lift F hF).map f ≫
        homMk (P := P) (X := (P.lift F hF).obj Y)
          (Y := (P.lift G hG).obj Y) (α.app Y) =
      homMk (P := P) (X := (P.lift F hF).obj X)
          (Y := (P.lift G hG).obj X) (α.app X) ≫
        (P.lift G hG).map f := sorry

/-- The natural transformation between full-subcategory lifts induced by an
ambient natural transformation. -/
@[stacks 001D "natural transformations between full-subcategory lifts"]
def liftNatTrans
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (α : F ⟶ G) : P.lift F hF ⟶ P.lift G hG :=
  (P.fullyFaithfulι.whiskeringRight C).preimage α

/-- The underlying ambient component of `liftNatTrans` is the original
component. -/
@[simp, stacks 001D "full-subcategory lifted transformation component"]
theorem liftNatTrans_app_hom
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (α : F ⟶ G) (X : C) :
    ((P.liftNatTrans hF hG α).app X).hom = α.app X := sorry

/-- Forgetting a lifted natural transformation recovers the ambient natural
transformation. -/
@[stacks 001D "forget a full-subcategory lifted transformation"]
theorem whiskerRight_liftNatTrans
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (α : F ⟶ G) :
    Functor.whiskerRight (P.liftNatTrans hF hG α) P.ι = α := sorry

/-- Lifting an identity natural transformation gives the identity of the
lifted functor. -/
@[simp]
theorem liftNatTrans_id (F : C ⥤ D) (hF : ∀ X, P (F.obj X)) :
    P.liftNatTrans hF hF (𝟙 F) = 𝟙 (P.lift F hF) := sorry

/-- Lifting natural transformations preserves vertical composition. -/
@[simp]
theorem liftNatTrans_comp
    {F G H : C ⥤ D}
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (hH : ∀ X, P (H.obj X)) (α : F ⟶ G) (β : G ⟶ H) :
    P.liftNatTrans hF hH (α ≫ β) =
      P.liftNatTrans hF hG α ≫ P.liftNatTrans hG hH β := sorry

/-- The natural isomorphism between full-subcategory lifts induced by an
ambient natural isomorphism. -/
@[stacks 001D "natural isomorphisms between full-subcategory lifts"]
def liftNatIso
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (e : F ≅ G) : P.lift F hF ≅ P.lift G hG :=
  (P.fullyFaithfulι.whiskeringRight C).preimageIso e

/-- The underlying ambient component of the forward map of `liftNatIso` is
the original forward component. -/
@[simp]
theorem liftNatIso_hom_app_hom
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (e : F ≅ G) (X : C) :
    ((P.liftNatIso hF hG e).hom.app X).hom = e.hom.app X := sorry

/-- The underlying ambient component of the inverse map of `liftNatIso` is
the original inverse component. -/
@[simp]
theorem liftNatIso_inv_app_hom
    {F G : C ⥤ D} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (e : F ≅ G) (X : C) :
    ((P.liftNatIso hF hG e).inv.app X).hom = e.inv.app X := sorry

end CategoryTheory.ObjectProperty
