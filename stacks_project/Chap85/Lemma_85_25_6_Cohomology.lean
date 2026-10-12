/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap85.Lemma_85_2_8_Morphism

/-!
# Stage pullbacks and cohomology of an augmentation

Pullback of an abelian sheaf on a space `X` along the degree-`n` map of an
augmentation of a simplicial space, and the cohomology groups `H^q(Y_p, F_p)`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/-- Inverse image of an abelian sheaf on `X` along the degree-`n` map of an
augmentation `a : Y ⟶ X`, landing on `Y_n`. This is the sheaf `F_n` of a
hypercovering spectral sequence. -/
def stageInverseImage (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}] :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u} :=
  (Opens.map (componentSpaceMap a n)).sheafPullback AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))

/-- `stageInverseImage a n` is sheaf pullback along `Opens.map` of `componentSpaceMap a n`. -/
theorem stageInverseImage_eq (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}] :
    stageInverseImage a n =
      (Opens.map (componentSpaceMap a n)).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) :=
  sorry

/-- Evaluating `stageInverseImage a n` on `F` is sheaf pullback of `F` along the degree-`n`
augmentation map. -/
theorem stageInverseImage_obj (n : ℕ)
    [HasWeakSheafify (Opens.grothendieckTopology (Y.obj (op ⦋n⦌))) AddCommGrpCat.{u}]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (stageInverseImage a n).obj F =
      ((Opens.map (componentSpaceMap a n)).sheafPullback AddCommGrpCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (Y.obj (op ⦋n⦌)))).obj F :=
  sorry

/-- The cohomology group `H^q(Y_p, F_p)` of the degree-`p` pullback of an abelian sheaf
along an augmentation. -/
abbrev stageCohomology (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    AddCommGrpCat.{v} :=
  (Sheaf.functorH (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) q).obj
    ((stageInverseImage a p).obj F)

/-- `stageCohomology a F p q` is `Sheaf.functorH` of `stageInverseImage a p` on `F`. -/
theorem stageCohomology_eq (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (p q : ℕ)
    [HasSheafify (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u}]
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) AddCommGrpCat.{u})] :
    stageCohomology a F p q =
      (Sheaf.functorH (Opens.grothendieckTopology (Y.obj (op ⦋p⦌))) q).obj
        ((stageInverseImage a p).obj F) :=
  sorry

end CategoryTheory.SimplicialObject

