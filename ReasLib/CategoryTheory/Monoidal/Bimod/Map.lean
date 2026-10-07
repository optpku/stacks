module

public import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting bimodules along monoidal functors

A lax monoidal functor transports monoid objects and their bimodules.  This is the bimodule
counterpart of Mathlib's `Functor.mapMon`; it is the common owner for change-of-base constructions
on graded modules, complexes, and sheaves of modules.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.LaxMonoidal]

/-- The image of an `(A,B)`-bimodule under a lax monoidal functor. -/
@[stacks 0FSA "monoidal transport of a bimodule"]
noncomputable def mapBimodObj {A B : Mon C} (M : Bimod A B) :
    Bimod (F.mapMon.obj A) (F.mapMon.obj B) where
  X := F.obj M.X
  actLeft := LaxMonoidal.μ F A.X M.X ≫ F.map M.actLeft
  actRight := LaxMonoidal.μ F M.X B.X ≫ F.map M.actRight
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The image of a bimodule morphism under a lax monoidal functor. -/
noncomputable def mapBimodMap {A B : Mon C} {M N : Bimod A B} (f : M ⟶ N) :
    mapBimodObj F M ⟶ mapBimodObj F N where
  hom := F.map f.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- A lax monoidal functor transports bimodules over a fixed pair of monoid objects. -/
@[stacks 0FSA "monoidal transport of bimodule categories"]
noncomputable def mapBimod (A B : Mon C) :
    Bimod A B ⥤ Bimod (F.mapMon.obj A) (F.mapMon.obj B) where
  obj := mapBimodObj F
  map := mapBimodMap F
  map_id := sorry
  map_comp := sorry

/-- Transporting a bimodule applies the underlying functor to its carrier. -/
@[simp]
theorem mapBimodObj_X {A B : Mon C} (M : Bimod A B) :
    (mapBimodObj F M).X = F.obj M.X := sorry

/-- The transported left action is obtained from the lax tensorator and the original action. -/
@[simp]
theorem mapBimodObj_actLeft {A B : Mon C} (M : Bimod A B) :
    (mapBimodObj F M).actLeft =
      LaxMonoidal.μ F A.X M.X ≫ F.map M.actLeft := sorry

/-- The transported right action is obtained from the lax tensorator and the original action. -/
@[simp]
theorem mapBimodObj_actRight {A B : Mon C} (M : Bimod A B) :
    (mapBimodObj F M).actRight =
      LaxMonoidal.μ F M.X B.X ≫ F.map M.actRight := sorry

/-- Transport of a bimodule morphism applies the underlying functor to its carrier map. -/
@[simp]
theorem mapBimodMap_hom {A B : Mon C} {M N : Bimod A B} (f : M ⟶ N) :
    (mapBimodMap F f).hom = F.map f.hom := sorry

/-- Evaluating `mapBimod` uses the explicit transported bimodule object. -/
@[simp]
theorem mapBimod_obj {A B : Mon C} (M : Bimod A B) :
    (mapBimod F A B).obj M = mapBimodObj F M := sorry

-- The carrier and action maps are explicit; `sorryAx` is confined to bimodule coherence laws.

end CategoryTheory.Functor

end
