module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import stacks_project.Chap85.Lemma_85_3_5

/-!
# Lemma 85.10.4

In Situation 85.3.3, for a sheaf of rings `O` on `C_total`, an object `U` of
`C_n`, and an `O`-module `F`, objectwise cohomology `H^p(U, F)` on `C_total`
agrees with `H^p(U, g_n^* F)` on `C_n`.
-/

@[expose] public section

open CategoryTheory Opposite
open RingedSite.Cocontinuous

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})

/-- Lemma 85.10.4 (1): in Situation 85.3.3 case A, for a sheaf of rings `O` on
`C_total`, `U` in `C_n`, and `F` in `Mod(O)`, the objectwise cohomology
`H^p((ofStage C n).obj U, F)` on `C_total` is isomorphic to `H^p(U, g_n^* F)`
on `C_n`. -/
@[stacks 0DH2]
theorem cohomologyOver_ofStage_iso
    [HasSheafify (topology C J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology C J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : C.obj n) (F : SheafOfModules.{max w v} O) (p : ℕ) :
    IsIsomorphic
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf O).obj F) ((ofStage C n).obj U) p)
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf
            (inverseImageRingSheaf (ofStage C n) O :
              Sheaf ((J n).toGrothendieck) RingCat.{w})).obj
          ((moduleInverseImage (ofStage C n) O).obj F)) U p) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})

/-- Lemma 85.10.4 (2): in Situation 85.3.3 case B, for a sheaf of rings `O` on
`C_total`, `U` in `C_n`, and `F` in `Mod(O)`, the objectwise cohomology
`H^p((ι F (op n)).obj U, F)` on `C_total` is isomorphic to `H^p(U, g_n^* F)`
on `C_n`. -/
@[stacks 0DH2]
theorem cohomologyOver_fiber_iso
    [HasSheafify (topology F J) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf (topology F J) AddCommGrpCat.{max w v})]
    (n : SimplexCategory)
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{max w v})]
    (U : F.obj (op n)) (M : SheafOfModules.{max w v} O) (p : ℕ) :
    IsIsomorphic
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf O).obj M) ((ι F (op n)).obj U) p)
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf
            (inverseImageRingSheaf (ι F (op n)) O :
              Sheaf ((J (op n)).toGrothendieck) RingCat.{w})).obj
          ((moduleInverseImage (ι F (op n)) O).obj M)) U p) :=
  sorry

end CategoryTheory.Grothendieck
