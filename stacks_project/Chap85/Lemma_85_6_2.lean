/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Acyclic
public import stacks_project.Chap85.Lemma_85_3_5

/-!
# Lemma 85.6.2

In Situation 85.3.3, if `O` is a sheaf of rings on `C_total` and `I` is injective
in `Mod(O)`, then the degree-`n` restriction `I_n` is a totally acyclic sheaf on
`C_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Lemma 85.6.2 (1): in Situation 85.3.3 case A, if `O` is a sheaf of rings on
`C_total` and `I` is injective in `Mod(O)`, then the restriction `I_n` is a
totally acyclic sheaf on `C_n`. -/
@[stacks 0D73, instance]
theorem isTotallyAcyclic_of_injective (n : SimplexCategory)
    (O : Sheaf (topology C J) RingCat.{w}) (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]
    [((ofStage C n).sheafPushforwardContinuous (Type w)
        (J n).toGrothendieck (topology C J)).IsRightAdjoint]
    [PreservesLimitsOfShape WalkingCospan
      ((ofStage C n).sheafPullback (Type w)
        (J n).toGrothendieck (topology C J))] :
    Sheaf.IsTotallyAcyclic
      ((stageRestrict C J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- Lemma 85.6.2 (2): in Situation 85.3.3 case B, if `O` is a sheaf of rings on
`C_total` and `I` is injective in `Mod(O)`, then the restriction `I_n` is a
totally acyclic sheaf on `C_n`. -/
@[stacks 0D73, instance]
theorem isTotallyAcyclic_of_injective (n : SimplexCategory)
    (O : Sheaf (topology F J) RingCat.{w}) (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]
    [((ι F (op n)).sheafPushforwardContinuous (Type w)
        (J (op n)).toGrothendieck (topology F J)).IsRightAdjoint]
    [PreservesLimitsOfShape WalkingCospan
      ((ι F (op n)).sheafPullback (Type w)
        (J (op n)).toGrothendieck (topology F J))] :
    Sheaf.IsTotallyAcyclic
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  sorry

end CategoryTheory.Grothendieck
