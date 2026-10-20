module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site
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

/-- A stage map carrying one diagram open into another also carries their componentwise
inverse images into one another along a morphism of simplicial spaces. -/
theorem zariskiMap.mapsTo {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    {U V : zariskiSite X} (g : U ⟶ V) :
    Set.MapsTo (Y.map g.base).hom
      ((Opens.map (f.app U.base)).obj U.opens)
      ((Opens.map (f.app V.base)).obj V.opens) := sorry

/-- Inverse image of a diagram-open arrow retains its stage map and pulls back its opens. -/
def zariskiMap.mapHom {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    {U V : zariskiSite X} (g : U ⟶ V) :
    DiagramOpens.ofOpens Y U.base ((Opens.map (f.app U.base)).obj U.opens) ⟶
      DiagramOpens.ofOpens Y V.base ((Opens.map (f.app V.base)).obj V.opens) :=
  DiagramOpens.homMk g.base (zariskiMap.mapsTo f g)

/-- Inverse image of diagram-open arrows preserves identity morphisms. -/
theorem zariskiMap.mapHom_id {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    (U : zariskiSite X) :
    zariskiMap.mapHom f (𝟙 U) =
      𝟙 (DiagramOpens.ofOpens Y U.base ((Opens.map (f.app U.base)).obj U.opens)) := sorry

/-- Inverse image of diagram-open arrows preserves composition. -/
theorem zariskiMap.mapHom_comp {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X)
    {U V W : zariskiSite X} (g : U ⟶ V) (h : V ⟶ W) :
    zariskiMap.mapHom f (g ≫ h) = zariskiMap.mapHom f g ≫ zariskiMap.mapHom f h := sorry

/-- The functor `zariskiSite X ⥤ zariskiSite Y` sending a stage open of `X` to its
inverse image under the corresponding component of `f : Y ⟶ X`. -/
def zariskiMap {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    zariskiSite X ⥤ zariskiSite Y where
  obj U := DiagramOpens.ofOpens Y U.base ((Opens.map (f.app U.base)).obj U.opens)
  map g := zariskiMap.mapHom f g
  map_id := zariskiMap.mapHom_id f
  map_comp := zariskiMap.mapHom_comp f

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

/-- Componentwise inverse image along a morphism of simplicial spaces is continuous and
representably flat for the Zariski topologies, inducing a morphism of sites from `Y` to `X`. -/
instance zariskiMap.isMorphismOfSites {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    IsMorphismOfSites (zariskiTopology X) (zariskiTopology Y) (zariskiMap f) := sorry

end CategoryTheory.SimplicialObject
