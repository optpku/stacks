module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped Simplicial CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable (X : SimplicialObject TopCat.{u}) (n : ℕ)

#check (component X n : Opens (X.obj (op ⦋n⦌)) ⥤ DiagramOpens X)
#check (TopCat.DiagramOpens.fiber_obj X (op ⦋n⦌) :
  ∀ U : Opens (X.obj (op ⦋n⦌)),
    (DiagramOpens.fiber X (op ⦋n⦌)).obj U = DiagramOpens.ofOpens X (op ⦋n⦌) U)
#check (componentMorphism X n : MorphismOfTopoiIn (zariskiTopology X)
  (Opens.grothendieckTopology (X.obj (op ⦋n⦌))))
#check (sheafComponent X n (Type u) : Sheaf (zariskiTopology X) (Type u) ⥤
  Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u))
#check (sheafLowerShriek X n :
  Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) (Type u) ⥤
    Sheaf (zariskiTopology X) (Type u))
#check (abelianLowerShriek X n :
  Sheaf (Opens.grothendieckTopology (X.obj (op ⦋n⦌))) AddCommGrpCat.{u} ⥤
    Sheaf (zariskiTopology X) AddCommGrpCat.{u})
#check (componentMorphism_inverseImage_iso_sheafComponent X n :
  (componentMorphism X n)⁻¹ ≅ sheafComponent X n (Type u))

end CategoryTheory.SimplicialObject
