/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.Cohomology
public import ReasLib.CategoryTheory.Sites.Grothendieck.Cohomology

/-!
# Lemma 85.8.6

In Situation 85.3.3, for `U` in `C_n` and `F` in `Ab(C_total)`, objectwise
cohomology `H^p(U, F)` on `C_total` (with `U` viewed in `C_total`) agrees with
`H^p(U, g_n⁻¹ F)` on `C_n`.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

/- Lemma 85.8.6: cohomology over a stage object agrees with cohomology after
restriction to the stage in case A of Situation 85.3.3. -/
@[stacks 0DBZ] #check (CategoryTheory.SimplicialSites.cohomologyOverObject_ofStage_iso :
    ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [IsMorphismDiagram C J]
    [HasSheafify (topology C J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology C J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : C.obj n) (F : Sheaf (topology C J) AddCommGrpCat.{max w v}) (p : ℕ),
    IsIsomorphic
      (Sheaf.cohomologyOverObject F ((ofStage C n).obj U) p)
      (Sheaf.cohomologyOverObject
        ((stageRestrict C J AddCommGrpCat.{max w v} n).obj F) U p))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

/- The same comparison in case B of Situation 85.3.3. -/
#check (CategoryTheory.Grothendieck.cohomologyOverObject_fiber_iso :
    ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    [IsFiberwiseSite F J]
    [HasSheafify (topology F J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology F J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : F.obj (op n)) (G : Sheaf (topology F J) AddCommGrpCat.{max w v})
    (p : ℕ),
    IsIsomorphic
      (Sheaf.cohomologyOverObject G ((ι F (op n)).obj U) p)
      (Sheaf.cohomologyOverObject
        ((fiberRestrict F J AddCommGrpCat.{max w v} n).obj G) U p))

end CategoryTheory.Grothendieck
