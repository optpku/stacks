/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Topology.Sheaves.Coproduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {I : Type u}
variable (F : I → X.Sheaf AddCommGrpCat.{u})
variable (U : Opens X) (x : X) (i : I)

/- Remark 111.32.8 (1): the coproduct of abelian sheaves is the sheafification of the
underlying presheaf coproduct. -/
@[stacks 02EX] #check
  (TopCat.Sheaf.coproductIsoSheafify F :
    ∐ F ≅
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (∐ fun j ↦ (forget AddCommGrpCat.{u} X).obj (F j)))

/- Remark 111.32.8 (2): the stalk of a coproduct of abelian sheaves is the coproduct of the
stalks. -/
@[stacks 02EX] #check
  (TopCat.Sheaf.stalkCoproductIso F x :
    (∐ F).presheaf.stalk x ≅ ∐ fun j ↦ (F j).presheaf.stalk x)

#check
  (CategoryTheory.Limits.sigmaObjIso (fun j ↦ (F j).presheaf) (op U) :
    (∐ fun j ↦ (F j).presheaf).obj (op U) ≅
      ∐ fun j ↦ (F j).presheaf.obj (op U))

#check
  (CategoryTheory.Limits.ι_comp_sigmaObjIso_hom (fun j ↦ (F j).presheaf) (op U) i :
    (Sigma.ι (fun j ↦ (F j).presheaf) i).app (op U) ≫
        (CategoryTheory.Limits.sigmaObjIso (fun j ↦ (F j).presheaf) (op U)).hom =
      Sigma.ι (fun j ↦ (F j).presheaf.obj (op U)) i)

#check
  (TopCat.Sheaf.stalkCoproductIso_ι F x i :
    (forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (Sigma.ι F i) ≫
      (TopCat.Sheaf.stalkCoproductIso F x).hom =
    Sigma.ι (fun j ↦ (F j).presheaf.stalk x) i)

end TopCat.Sheaf

end

end
