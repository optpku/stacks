module

public import stacks_project.Chap85.Lemma_85_2_1_Site
public import ReasLib.CategoryTheory.Sites.MorphismOfSites

/-!
# Inverse image on the Zariski site of a simplicial space

A morphism of simplicial spaces induces a functor of Zariski sites by
degreewise inverse image of opens.
-/

@[expose]
public section

universe u

open CategoryTheory TopologicalSpace TopCat

namespace CategoryTheory.SimplicialObject

/-- The functor `u : zariskiSite X ⥤ zariskiSite Y` sending an open of a stage of `X`
to its inverse image under the corresponding component of `f : Y ⟶ X`. -/
def zariskiMap {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    zariskiSite X ⥤ zariskiSite Y where
  obj U := DiagramOpens.ofOpens Y U.base ((Opens.map (f.app U.base)).obj U.opens)
  map g := DiagramOpens.homMk g.base sorry
  map_id := sorry
  map_comp := sorry

/-- `zariskiMap f` sends `DiagramOpens.ofOpens X c U` to the inverse image of `U` along
`f.app c`. -/
@[simp]
theorem zariskiMap_obj_ofOpens {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    (c : SimplexCategoryᵒᵖ) (U : Opens (X.obj c)) :
    (zariskiMap f).obj (DiagramOpens.ofOpens X c U) =
      DiagramOpens.ofOpens Y c ((Opens.map (f.app c)).obj U) :=
  rfl

/-- `zariskiMap f` preserves the underlying stage morphism of a morphism of diagram opens. -/
@[simp]
theorem zariskiMap_map_base {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    {U V : zariskiSite X} (g : U ⟶ V) :
    ((zariskiMap f).map g).base = g.base :=
  rfl

end CategoryTheory.SimplicialObject
