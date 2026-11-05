module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map
public import ReasLib.Algebra.Homology.HomotopyCategory.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality

@[expose] public section

/-!
# Naturality of the bounded-above homotopy functor

Natural transformations and natural isomorphisms of additive functors restrict to the
bounded-above homotopy categories. The construction is the specialization of the neutral
full-subcategory restriction API.
-/

open CategoryTheory
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Minus

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

/-- An additive natural transformation induces a natural transformation on
bounded-above homotopy categories. -/
@[stacks 014X "bounded-above homotopy natural transformation"]
def natTrans (α : F ⟶ G) :
    F.mapHomotopyCategoryMinus ⟶ G.mapHomotopyCategoryMinus :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (NatTrans.mapHomotopyCategory α (up ℤ))

/-- The underlying component of the bounded-above homotopy natural transformation is the
ambient homotopy-category component. -/
@[simp]
theorem natTrans_app_hom (α : F ⟶ G) (K : HomotopyCategory.Minus C) :
    ((natTrans α).app K).hom =
      (NatTrans.mapHomotopyCategory α (up ℤ)).app K.obj := sorry

/-- The bounded-above homotopy action preserves identity natural transformations. -/
@[simp]
theorem natTrans_id : natTrans (𝟙 F) = 𝟙 F.mapHomotopyCategoryMinus := sorry

/-- The bounded-above homotopy action preserves composition of natural transformations. -/
@[simp]
theorem natTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    natTrans (α ≫ β) = natTrans α ≫ natTrans β := sorry

/-- An additive natural isomorphism induces a natural isomorphism on bounded-above
homotopy categories. -/
@[stacks 014X "bounded-above homotopy natural isomorphism"]
def natIso (e : F ≅ G) :
    F.mapHomotopyCategoryMinus ≅ G.mapHomotopyCategoryMinus :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (NatIso.mapHomotopyCategory e (up ℤ))

/-- The forward map of the induced bounded-above natural isomorphism is the induced
natural transformation. -/
@[simp]
theorem natIso_hom (e : F ≅ G) : (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of the induced bounded-above natural isomorphism is the induced
natural transformation in the reverse direction. -/
@[simp]
theorem natIso_inv (e : F ≅ G) : (natIso e).inv = natTrans e.inv := sorry

/-- The underlying forward component of the bounded-above homotopy natural isomorphism is
the ambient homotopy-category component. -/
@[simp]
theorem natIso_hom_app_hom (e : F ≅ G) (K : HomotopyCategory.Minus C) :
    ((natIso e).hom.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded-above homotopy natural isomorphism is
the ambient homotopy-category component. -/
@[simp]
theorem natIso_inv_app_hom (e : F ≅ G) (K : HomotopyCategory.Minus C) :
    ((natIso e).inv.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).inv.app K.obj := sorry



end CategoryTheory.Functor.Homotopy.Minus
