module

public import ReasLib.Topology.Sheaves.Simplicial.Functoriality

open CategoryTheory TopologicalSpace TopCat
universe u
namespace CategoryTheory.SimplicialObject
variable {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) (n : SimplexCategoryᵒᵖ)

/- Lemma 85.2.4: the degreewise square for inverse image of opens. -/
#check (CategoryTheory.SimplicialObject.zariskiMap_fiber f n :
    DiagramOpens.fiber X n ⋙ zariskiMap f ≅
      Opens.map (f.app n) ⋙ DiagramOpens.fiber Y n)

variable [HasWeakSheafify (zariskiTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology (Y.obj n)) (Type u)]
variable [∀ P : (zariskiSite X)ᵒᵖ ⥤ Type u, (zariskiMap f).op.HasLeftKanExtension P]
variable [∀ P : (Opens (X.obj n))ᵒᵖ ⥤ Type u, (Opens.map (f.app n)).op.HasLeftKanExtension P]

/- Lemma 85.2.4: the natural componentwise inverse-image comparison. -/
#check (CategoryTheory.SimplicialObject.zariskiMap_pullbackRestrict f n :
    (zariskiMap f).sheafPullback (Type u) (zariskiTopology X) (zariskiTopology Y) ⋙
      sheafFiber Y n (Type u) ≅
    sheafFiber X n (Type u) ⋙ TopCat.Sheaf.pullback (Type u) (f.app n))

end CategoryTheory.SimplicialObject
