/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement.Functoriality
public import ReasLib.CategoryTheory.Pro.Sequential.Quotient

/-!
# Functoriality of sequential pro-morphism classes

Postcomposition of sequential representatives descends to their common-refinement classes.  The
resulting operation retains the representative-level identity and composition laws and preserves
invertibility of the associated pro-morphism.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory.Pro.SequentialHom.Quotient

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {X Y : ℕᵒᵖ ⥤ C}

/-- Postcompose a common-refinement class of sequential representatives by a functor. -/
def map (q : Pro.SequentialHom.Quotient (X := X) (Y := Y)) (F : C ⥤ D) :
    Pro.SequentialHom.Quotient (X := X ⋙ F) (Y := Y ⋙ F) :=
  _root_.Quotient.map (fun r ↦ r.map F)
    (fun _ _ h ↦ Equivalent.map h F) q

/-- Mapping the class of a representative gives the class of its stagewise image. -/
@[simp]
theorem map_mk (r : Pro.SequentialHom X Y) (F : C ⥤ D) :
    map (_root_.Quotient.mk (setoid (X := X) (Y := Y)) r) F =
      _root_.Quotient.mk (setoid (X := X ⋙ F) (Y := Y ⋙ F)) (r.map F) := sorry

/-- Postcomposition by the identity functor fixes every common-refinement class. -/
@[simp]
theorem map_id (q : Pro.SequentialHom.Quotient (X := X) (Y := Y)) :
    map q (𝟭 C) = q := sorry

/-- Successive postcomposition agrees with postcomposition by the composite functor. -/
@[simp]
theorem map_comp {E : Type uE} [Category.{vE} E]
    (q : Pro.SequentialHom.Quotient (X := X) (Y := Y)) (F : C ⥤ D) (G : D ⥤ E) :
    map (map q F) G = map q (F ⋙ G) := sorry

/-- Stagewise functorial postcomposition preserves invertibility of the associated pro-morphism.
-/
theorem toHom_map_isIso
    (q : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    (h : IsIso (quotientToHom q)) (F : C ⥤ D) :
    IsIso (quotientToHom (map q F)) := sorry

end CategoryTheory.Pro.SequentialHom.Quotient
