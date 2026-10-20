/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Simplicial.Stage

/-!
# Objectwise cohomology and restriction to a stage of a simplicial site
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Objectwise cohomology over a stage object agrees with cohomology on that stage
after restricting the coefficient sheaf from the total site. -/
@[stacks 0DBZ]
theorem cohomologyOverObject_ofStage_iso
    [HasSheafify (topology C J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology C J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : C.obj n) (F : Sheaf (topology C J) AddCommGrpCat.{max w v}) (p : ℕ) :
    IsIsomorphic
      (Sheaf.cohomologyOverObject F ((ofStage C n).obj U) p)
      (Sheaf.cohomologyOverObject
        ((stageRestrict C J AddCommGrpCat.{max w v} n).obj F) U p) :=
  sorry

end CategoryTheory.SimplicialSites
