/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map

@[expose] public section

/-!
# Computation for functors on bounded homotopy categories

This file exposes the underlying object, morphism, inclusion-comparison, and
composition-comparison data of the three boundedness variants. Downstream code can
simplify through the bounded full subcategories without unfolding their construction.
-/

open CategoryTheory
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

namespace Plus

/-- Objectwise computation for the bounded-below homotopy functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Plus C) :
    (F.mapHomotopyCategoryPlus.obj K).obj =
      (F.mapHomotopyCategory (up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded-below homotopy functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) [F.Additive]
    {K L : HomotopyCategory.Plus C} (f : K ⟶ L) :
    (F.mapHomotopyCategoryPlus.map f).hom =
      (F.mapHomotopyCategory (up ℤ)).map f.hom := sorry

/-- The forward inclusion comparison for the bounded-below homotopy functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_hom_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Plus C) :
    (compInclusionIso F).hom.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

/-- The inverse inclusion comparison for the bounded-below homotopy functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_inv_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Plus C) :
    (compInclusionIso F).inv.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

end Plus

namespace Minus

/-- Objectwise computation for the bounded-above homotopy functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Minus C) :
    (F.mapHomotopyCategoryMinus.obj K).obj =
      (F.mapHomotopyCategory (up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded-above homotopy functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) [F.Additive]
    {K L : HomotopyCategory.Minus C} (f : K ⟶ L) :
    (F.mapHomotopyCategoryMinus.map f).hom =
      (F.mapHomotopyCategory (up ℤ)).map f.hom := sorry

/-- The forward inclusion comparison for the bounded-above homotopy functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_hom_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Minus C) :
    (compInclusionIso F).hom.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

/-- The inverse inclusion comparison for the bounded-above homotopy functor is
componentwise the identity. -/
@[simp]
theorem compInclusionIso_inv_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Minus C) :
    (compInclusionIso F).inv.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

/-- The underlying forward component of the bounded-above composition comparison is the
ambient homotopy-category comparison. -/
@[simp]
theorem compIso_hom_app_hom
    {E : Type*} [Category E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (K : HomotopyCategory.Minus C) :
    ((compIso e).hom.app K).hom =
      (Functor.mapHomotopyCategoryCompIso e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded-above composition comparison is the
ambient homotopy-category comparison. -/
@[simp]
theorem compIso_inv_app_hom
    {E : Type*} [Category E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (K : HomotopyCategory.Minus C) :
    ((compIso e).inv.app K).hom =
      (Functor.mapHomotopyCategoryCompIso e (up ℤ)).inv.app K.obj := sorry

end Minus

namespace Bounded

/-- Objectwise computation for the bounded homotopy functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Bounded C) :
    (F.mapHomotopyCategoryBounded.obj K).obj =
      (F.mapHomotopyCategory (up ℤ)).obj K.obj := sorry

/-- Morphismwise computation for the bounded homotopy functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) [F.Additive]
    {K L : HomotopyCategory.Bounded C} (f : K ⟶ L) :
    (F.mapHomotopyCategoryBounded.map f).hom =
      (F.mapHomotopyCategory (up ℤ)).map f.hom := sorry

/-- The forward inclusion comparison for the bounded homotopy functor is componentwise the
identity. -/
@[simp]
theorem compInclusionIso_hom_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Bounded C) :
    (compInclusionIso F).hom.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

/-- The inverse inclusion comparison for the bounded homotopy functor is componentwise the
identity. -/
@[simp]
theorem compInclusionIso_inv_app (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Bounded C) :
    (compInclusionIso F).inv.app K =
      𝟙 ((F.mapHomotopyCategory (up ℤ)).obj K.obj) := sorry

/-- The underlying forward component of the bounded composition comparison is the ambient
homotopy-category comparison. -/
@[simp]
theorem compIso_hom_app_hom
    {E : Type*} [Category E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (K : HomotopyCategory.Bounded C) :
    ((compIso e).hom.app K).hom =
      (Functor.mapHomotopyCategoryCompIso e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded composition comparison is the ambient
homotopy-category comparison. -/
@[simp]
theorem compIso_inv_app_hom
    {E : Type*} [Category E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.Additive]
    (K : HomotopyCategory.Bounded C) :
    ((compIso e).inv.app K).hom =
      (Functor.mapHomotopyCategoryCompIso e (up ℤ)).inv.app K.obj := sorry

end Bounded


end CategoryTheory.Functor.Homotopy
