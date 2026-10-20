module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Site
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Restriction to stages of a simplicial Zariski site

The Zariski site and its topology are owned by `TopCat.DiagramOpens`. This leaf supplies the
inverse-image-open arrows and restrictions of sheaves needed to describe a sheaf as a system
on the stages of the simplicial space.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace TopCat

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u})

/-- The arrow from an inverse-image open to the original open, over its given stage map. -/
def pullbackHom {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (V : Opens (X.obj m)) :
    DiagramOpens.ofOpens X n ((Opens.map (X.map f)).obj V) ⟶
      DiagramOpens.ofOpens X m V :=
  DiagramOpens.homMk f (fun _ hx ↦ hx)

/-- The stage map of the inverse-image-open arrow is the supplied map. -/
@[simp] theorem pullbackHom_base {n m : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (V : Opens (X.obj m)) : (pullbackHom X f V).base = f := rfl

variable (C : Type v) [Category.{w} C]

/-- Restriction of a sheaf on the simplicial Zariski site to the opens of a stage. -/
def restrictToDegree (n : SimplexCategory) :
    Sheaf (zariskiTopology X) C ⥤ (X.obj (op n)).Sheaf C where
  obj F := ⟨(DiagramOpens.fiber X (op n)).op ⋙ F.obj, sorry⟩
  map {F G} α :=
    ⟨{ app := fun V ↦ α.hom.app ((DiagramOpens.fiber X (op n)).op.obj V),
       naturality := sorry }⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying restricted presheaf is composition with the canonical stage inclusion. -/
theorem restrictToDegree_obj (n : SimplexCategory) (F : Sheaf (zariskiTopology X) C) :
    ((restrictToDegree X C n).obj F).presheaf =
      (DiagramOpens.fiber X (op n)).op ⋙ F.obj := rfl

end CategoryTheory.SimplicialObject
