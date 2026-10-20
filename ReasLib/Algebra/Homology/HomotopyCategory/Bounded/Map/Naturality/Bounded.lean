/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map
public import ReasLib.Algebra.Homology.HomotopyCategory.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Naturality

@[expose] public section

/-!
# Naturality of the bounded homotopy functor

Natural transformations and natural isomorphisms of additive functors restrict to the
bounded homotopy categories. The construction is the specialization of the neutral
full-subcategory restriction API.
-/

open CategoryTheory
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Bounded

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

/-- An additive natural transformation induces a natural transformation on bounded
homotopy categories. -/
@[stacks 014X "bounded homotopy natural transformation"]
def natTrans (α : F ⟶ G) :
    F.mapHomotopyCategoryBounded ⟶ G.mapHomotopyCategoryBounded :=
  ObjectProperty.FullSubcategory.restrict.natTrans
    (mapsTo F) (mapsTo G) (NatTrans.mapHomotopyCategory α (up ℤ))

/-- The underlying component of the bounded homotopy natural transformation is the ambient
homotopy-category component. -/
@[simp]
theorem natTrans_app_hom (α : F ⟶ G) (K : HomotopyCategory.Bounded C) :
    ((natTrans α).app K).hom =
      (NatTrans.mapHomotopyCategory α (up ℤ)).app K.obj := sorry

/-- The bounded homotopy action preserves identity natural transformations. -/
@[simp]
theorem natTrans_id : natTrans (𝟙 F) = 𝟙 F.mapHomotopyCategoryBounded := sorry

/-- The bounded homotopy action preserves composition of natural transformations. -/
@[simp]
theorem natTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    natTrans (α ≫ β) = natTrans α ≫ natTrans β := sorry

/-- An additive natural isomorphism induces a natural isomorphism on bounded homotopy
categories. -/
@[stacks 014X "bounded homotopy natural isomorphism"]
def natIso (e : F ≅ G) :
    F.mapHomotopyCategoryBounded ≅ G.mapHomotopyCategoryBounded :=
  ObjectProperty.FullSubcategory.restrict.natIso
    (mapsTo F) (mapsTo G) (NatIso.mapHomotopyCategory e (up ℤ))

/-- The forward map of the induced bounded natural isomorphism is the induced natural
transformation. -/
@[simp]
theorem natIso_hom (e : F ≅ G) : (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of the induced bounded natural isomorphism is the induced natural
transformation in the reverse direction. -/
@[simp]
theorem natIso_inv (e : F ≅ G) : (natIso e).inv = natTrans e.inv := sorry

/-- The underlying forward component of the bounded homotopy natural isomorphism is the
ambient homotopy-category component. -/
@[simp]
theorem natIso_hom_app_hom (e : F ≅ G) (K : HomotopyCategory.Bounded C) :
    ((natIso e).hom.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded homotopy natural isomorphism is the
ambient homotopy-category component. -/
@[simp]
theorem natIso_inv_app_hom (e : F ≅ G) (K : HomotopyCategory.Bounded C) :
    ((natIso e).inv.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).inv.app K.obj := sorry



end CategoryTheory.Functor.Homotopy.Bounded
