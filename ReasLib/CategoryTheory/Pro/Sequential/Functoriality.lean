/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.Presentation

/-!
# Functoriality of sequential pro-morphism representatives

Sequential representatives can be postcomposed with any functor without changing their monotone
reindexing. This leaf keeps that concrete operation separate from the quotient comparison and from
special constructors such as shifts.
-/

@[expose] public section

open CategoryTheory Opposite

universe uC vC uD vD uE vE

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {X Y : ℕᵒᵖ ⥤ C}

/-- Postcompose a sequential pro-morphism representative with a functor. Its monotone reindexing
is retained and its level maps are mapped by the functor. -/
def map (r : Pro.SequentialHom X Y) (F : C ⥤ D) :
    Pro.SequentialHom (X ⋙ F) (Y ⋙ F) where
  reindex := r.reindex
  hom :=
    { app := fun i ↦ F.map (r.hom.app i)
      naturality := fun _ _ _ ↦ sorry }

/-- Functorial postcomposition retains the representative's monotone reindexing. -/
@[simp]
theorem map_reindex (r : Pro.SequentialHom X Y) (F : C ⥤ D) :
    (r.map F).reindex = r.reindex := sorry

/-- The level map after functorial postcomposition is the image of the original level map. -/
@[simp]
theorem map_hom_app (r : Pro.SequentialHom X Y) (F : C ⥤ D) (n : ℕᵒᵖ) :
    (r.map F).hom.app n = F.map (r.hom.app n) := sorry

/-- Postcomposition of a sequential representative by the identity functor is unchanged. -/
@[simp]
theorem map_id (r : Pro.SequentialHom X Y) : r.map (𝟭 C) = r := sorry

/-- Postcomposition of a sequential representative respects functor composition. -/
@[simp]
theorem map_comp {E : Type uE} [Category.{vE} E] (r : Pro.SequentialHom X Y)
    (F : C ⥤ D) (G : D ⥤ E) :
    (r.map F).map G = r.map (F ⋙ G) := sorry

end CategoryTheory.Pro.SequentialHom
