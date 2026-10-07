module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap85.Lemma_85_3_5

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

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Lemma 85.8.6 (1): in Situation 85.3.3 case A, for `U` in `C_n` and `F` in
`Ab(C_total)`, the objectwise cohomology `H^p((ofStage C n).obj U, F)` on
`C_total` is isomorphic to `H^p(U, g_n⁻¹ F)` on `C_n`. -/
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

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- Lemma 85.8.6 (2): in Situation 85.3.3 case B, for `U` in `C_n` and `G` in
`Ab(C_total)`, the objectwise cohomology `H^p((ι F (op n)).obj U, G)` on
`C_total` is isomorphic to `H^p(U, g_n⁻¹ G)` on `C_n`. -/
@[stacks 0DBZ]
theorem cohomologyOverObject_fiber_iso
    [HasSheafify (topology F J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology F J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : F.obj (op n)) (G : Sheaf (topology F J) AddCommGrpCat.{max w v})
    (p : ℕ) :
    IsIsomorphic
      (Sheaf.cohomologyOverObject G ((ι F (op n)).obj U) p)
      (Sheaf.cohomologyOverObject
        ((fiberRestrict F J AddCommGrpCat.{max w v} n).obj G) U p) :=
  sorry

end CategoryTheory.Grothendieck
