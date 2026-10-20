module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.SimplicialMap
import StacksCheckRecall

@[expose]
public section

universe u

open CategoryTheory

namespace CategoryTheory.SimplicialObject

/- Lemma 85.2.3: a morphism `f : Y ⟶ X` of simplicial spaces induces the functor
`u = zariskiMap f : zariskiSite X ⥤ zariskiSite Y` sending an open `U ⊂ X.obj c` to
`(Opens.map (f.app c)).obj U ⊂ Y.obj c`, and this functor is a morphism of
sites `f_Zar : Y_Zar ⟶ X_Zar`. -/
@[stacks 09VN] #check (CategoryTheory.SimplicialObject.zariskiMap.isMorphismOfSites :
  ∀ {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X),
    IsMorphismOfSites (zariskiTopology X) (zariskiTopology Y) (zariskiMap f))

end CategoryTheory.SimplicialObject
