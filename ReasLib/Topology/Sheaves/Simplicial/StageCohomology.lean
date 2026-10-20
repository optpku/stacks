module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant

/-!
# Stage pullbacks and cohomology of an augmentation

Degreewise inverse image of abelian sheaves along an augmentation of a
simplicial topological space, and the cohomology of those inverse images.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- Inverse image of abelian sheaves along the degree-`n` component of an augmentation. -/
def stageInverseImage (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}] :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u} :=
  (Opens.map (show Y.obj (op ⦋n⦌) ⟶ X from a.app (op ⦋n⦌))).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- Degreewise inverse image is sheaf pullback along the augmentation component. -/
theorem stageInverseImage_eq (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}] :
    stageInverseImage a n =
      (Opens.map (show Y.obj (op ⦋n⦌) ⟶ X from a.app (op ⦋n⦌))).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  rfl

/-- Evaluating degreewise inverse image on a sheaf gives its pullback along the
corresponding augmentation component. -/
theorem stageInverseImage_obj (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (stageInverseImage a n).obj F =
      ((Opens.map (show Y.obj (op ⦋n⦌) ⟶ X from a.app (op ⦋n⦌))).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).obj F :=
  rfl

/-- The cohomology group of the degree-`p` inverse image of an abelian sheaf along
an augmentation. -/
abbrev stageCohomology (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    AddCommGrpCat.{v} :=
  (Sheaf.functorH (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) q).obj
    ((stageInverseImage a p).obj F)

/-- Stage cohomology is sheaf cohomology of the degreewise inverse image. -/
theorem stageCohomology_eq (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    stageCohomology a F p q =
      (Sheaf.functorH (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) q).obj
        ((stageInverseImage a p).obj F) :=
  rfl

end CategoryTheory.SimplicialObject
