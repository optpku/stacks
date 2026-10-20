/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Cohomology
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation

/-!
# Cohomology on simplicial family localizations

Objectwise cohomology on the total localization site compares with cohomology
on each component slice of a simplicial stage.
-/

@[expose] public section

universe w v u z

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))

/-- The fiber inclusion of a simplicial family localization is continuous. -/
instance totalSite_ι_isContinuous (n : SimplexCategory) :
    (Grothendieck.ι (overSiteDiagram K) (op n)).IsContinuous
      (overTopology J (K.obj (op n))) (overSiteTotalTopology J K) :=
  sorry

/-- Objectwise cohomology at a component object of a simplicial family localization is
isomorphic to cohomology of the corresponding restricted component sheaf. -/
theorem cohomologyOverObject_component_iso
    (n : SimplexCategory) (i : (K.obj (op n)).I)
    (U : overSlice (K.obj (op n)) i)
    (F : Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}) (p : ℕ)
    [HasSheafify (overSiteTotalTopology J K) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (overSiteTotalTopology J K) AddCommGrpCat.{max w u v})]
    [HasSheafify (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v}]
    [HasExt.{z} (Sheaf (J.over ((K.obj (op n)).obj i)) AddCommGrpCat.{max w u v})] :
    IsIsomorphic
      (Sheaf.cohomologyOverObject.{z, 0} F
        ((Grothendieck.ι (overSiteDiagram K) (op n)).obj
          ((overIncl (K.obj (op n)) i).obj U)) p)
      (Sheaf.cohomologyOverObject.{z, max w u}
        ((abelianComponentRestrict J (K.obj (op n)) i).obj
          (((Grothendieck.ι (overSiteDiagram K) (op n)).sheafPushforwardContinuous
              AddCommGrpCat.{max w u v}
              (overTopology J (K.obj (op n))) (overSiteTotalTopology J K)).obj F))
        U p) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
