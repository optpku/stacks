/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map
public import ReasLib.Algebra.Homology.HomotopyCategory.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Naturality

@[expose] public section

/-!
# Naturality of the bounded-below homotopy functor

Natural transformations and natural isomorphisms of additive functors descend to the
bounded-below homotopy categories. Their components are determined by the ambient
homotopy-category action.
-/

noncomputable section

open CategoryTheory
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Plus

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

/-- An additive natural transformation induces a natural transformation on
bounded-below homotopy categories. -/
@[stacks 014X "bounded-below homotopy natural transformation"]
noncomputable def natTrans (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus :=
  (HomotopyCategory.plus D).liftNatTrans
    (fun K => (F.mapHomotopyCategoryPlus.obj K).property)
    (fun K => (G.mapHomotopyCategoryPlus.obj K).property)
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
      (NatTrans.mapHomotopyCategory α (up ℤ)))

/-- The underlying component of the bounded-below homotopy natural transformation is the
ambient homotopy-category component. -/
@[simp]
theorem natTrans_app_hom (α : F ⟶ G) (K : HomotopyCategory.Plus C) :
    ((natTrans α).app K).hom =
      (NatTrans.mapHomotopyCategory α (up ℤ)).app K.obj := sorry

/-- The bounded-below homotopy action preserves identity natural transformations. -/
@[simp]
theorem natTrans_id : natTrans (𝟙 F) = 𝟙 F.mapHomotopyCategoryPlus := sorry

/-- The bounded-below homotopy action preserves composition of natural transformations. -/
@[simp]
theorem natTrans_comp (α : F ⟶ G) (β : G ⟶ H) :
    natTrans (α ≫ β) = natTrans α ≫ natTrans β := sorry

namespace natTrans

/-- An invertible additive transformation induces an invertible transformation on bounded-below
homotopy categories. -/
@[stacks 014X "isomorphism preservation for bounded-below homotopy naturality"]
noncomputable instance isIso (α : F ⟶ G) [IsIso α] : IsIso (natTrans α) := sorry

end natTrans

/-- An additive natural isomorphism induces a natural isomorphism on bounded-below
homotopy categories. -/
@[stacks 014X "bounded-below homotopy natural isomorphism"]
noncomputable def natIso (e : F ≅ G) :
    F.mapHomotopyCategoryPlus ≅ G.mapHomotopyCategoryPlus where
  hom := natTrans e.hom
  inv := natTrans e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the induced bounded-below natural isomorphism is the induced
natural transformation. -/
@[simp]
theorem natIso_hom (e : F ≅ G) : (natIso e).hom = natTrans e.hom := sorry

/-- The inverse map of the induced bounded-below natural isomorphism is the induced
natural transformation in the reverse direction. -/
@[simp]
theorem natIso_inv (e : F ≅ G) : (natIso e).inv = natTrans e.inv := sorry

/-- The underlying forward component of the bounded-below homotopy natural isomorphism is
the ambient homotopy-category component. -/
@[simp]
theorem natIso_hom_app_hom (e : F ≅ G) (K : HomotopyCategory.Plus C) :
    ((natIso e).hom.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).hom.app K.obj := sorry

/-- The underlying inverse component of the bounded-below homotopy natural isomorphism is
the ambient homotopy-category component. -/
@[simp]
theorem natIso_inv_app_hom (e : F ≅ G) (K : HomotopyCategory.Plus C) :
    ((natIso e).inv.app K).hom =
      (NatIso.mapHomotopyCategory e (up ℤ)).inv.app K.obj := sorry



end CategoryTheory.Functor.Homotopy.Plus
