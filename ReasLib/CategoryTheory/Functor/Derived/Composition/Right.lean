/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition Comparisons for Right Derived Functors

This file constructs the comparison from a chosen right derived model of a composite to the
composite of two chosen models. The construction is neutral in both localization functors and
does not require the two intermediate models themselves to satisfy a universal property.
-/

universe vA vB vC vDA vDB uA uB uC uDA uDB

namespace CategoryTheory

namespace Functor

namespace RightDerived.Composition

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {DA : Type uDA} {DB : Type uDB}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vDA} DA] [Category.{vDB} DB]
  {F : A ⥤ B} {G : B ⥤ C} {L : A ⥤ DA} {L' : B ⥤ DB}
  {RF : DA ⥤ DB} {RG : DB ⥤ C} {RGF : DA ⥤ C}

/-- The unit obtained by composing chosen right-derived model data for F and G. -/
def iteratedUnit
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG) :
    F ⋙ G ⟶ L ⋙ (RF ⋙ RG) :=
  whiskerLeft F αG ≫
    (associator F L' RG).hom ≫
    whiskerRight αF RG ≫
    (associator L RF RG).hom

set_option backward.isDefEq.respectTransparency false in
/-- The component of the iterated right-derived unit is the composite of the two unit
components. -/
@[simp]
theorem iteratedUnit_app
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (X : A) :
    (iteratedUnit αF αG).app X =
      αG.app (F.obj X) ≫ RG.map (αF.app X) := by
  simp [iteratedUnit]
  erw [← Category.assoc, Category.comp_id]

/-- The comparison from a chosen right-derived model of F ⋙ G to the composite of chosen
models of F and G. Only the model of F ⋙ G must satisfy the universal property. -/
@[stacks 05T2]
noncomputable def comparisonOfModels
    (S : MorphismProperty A)
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (αGF : F ⋙ G ⟶ L ⋙ RGF)
    [L.IsLocalization S]
    [RGF.IsRightDerivedFunctor αGF S] :
    RGF ⟶ RF ⋙ RG :=
  RGF.rightDerivedDesc αGF S (RF ⋙ RG) (iteratedUnit αF αG)

/-- The right-derived model comparison factors the composite unit through the iterated unit. -/
@[reassoc (attr := simp)]
theorem comparisonOfModels_fac
    (S : MorphismProperty A)
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (αGF : F ⋙ G ⟶ L ⋙ RGF)
    [L.IsLocalization S]
    [RGF.IsRightDerivedFunctor αGF S] :
    αGF ≫ whiskerLeft L (comparisonOfModels S αF αG αGF) =
      iteratedUnit αF αG := by
  exact RGF.rightDerived_fac αGF S (RF ⋙ RG) (iteratedUnit αF αG)

/-- The componentwise factorization equation for the right-derived model comparison. -/
theorem comparisonOfModels_fac_app
    (S : MorphismProperty A)
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (αGF : F ⋙ G ⟶ L ⋙ RGF)
    [L.IsLocalization S]
    [RGF.IsRightDerivedFunctor αGF S]
    (X : A) :
    αGF.app X ≫ (comparisonOfModels S αF αG αGF).app (L.obj X) =
      (iteratedUnit αF αG).app X := by
  exact RGF.rightDerived_fac_app αGF S (RF ⋙ RG) (iteratedUnit αF αG) X

set_option backward.isDefEq.respectTransparency false in
/-- At an object represented by the localization functor, invertibility of the comparison is
equivalent to invertibility of the iterated unit when the direct unit is invertible. -/
theorem comparisonOfModels_app_isIso_iff
    (S : MorphismProperty A)
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (αGF : F ⋙ G ⟶ L ⋙ RGF)
    [L.IsLocalization S]
    [RGF.IsRightDerivedFunctor αGF S]
    (X : A)
    [IsIso (αGF.app X)] :
    IsIso ((comparisonOfModels S αF αG αGF).app (L.obj X)) ↔
      IsIso ((iteratedUnit αF αG).app X) := by
  rw [← comparisonOfModels_fac_app S αF αG αGF X]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Invertible component units make the right-derived model comparison invertible at the
corresponding localized object. -/
instance comparisonOfModels_app_isIso
    (S : MorphismProperty A)
    (αF : F ⋙ L' ⟶ L ⋙ RF)
    (αG : G ⟶ L' ⋙ RG)
    (αGF : F ⋙ G ⟶ L ⋙ RGF)
    [L.IsLocalization S]
    [RGF.IsRightDerivedFunctor αGF S]
    (X : A)
    [IsIso (αF.app X)]
    [IsIso (αG.app (F.obj X))]
    [IsIso (αGF.app X)] :
    IsIso ((comparisonOfModels S αF αG αGF).app (L.obj X)) := by
  rw [comparisonOfModels_app_isIso_iff S αF αG αGF X, iteratedUnit_app]
  infer_instance

end RightDerived.Composition

end Functor

end CategoryTheory

/-! The square helper uses independent universes for the four source/target categories. -/

namespace CategoryTheory

namespace Functor.RightDerived.Composition

universe uA' uB' uC' uD' uLA' uLB' uLC' uLD'
  vA' vB' vC' vD' vLA' vLB' vLC' vLD'

variable {A : Type uA'} {B : Type uB'} {C : Type uC'} {D : Type uD'}
  {LAObj : Type uLA'} {LBObj : Type uLB'} {LCObj : Type uLC'} {LDObj : Type uLD'}
  [Category.{vA'} A] [Category.{vB'} B] [Category.{vC'} C] [Category.{vD'} D]
  [Category.{vLA'} LAObj] [Category.{vLB'} LBObj]
  [Category.{vLC'} LCObj] [Category.{vLD'} LDObj]
  {P : A ⥤ B} {UC : B ⥤ C} {UD : A ⥤ D} {Q : D ⥤ C}
  {L_A : A ⥤ LAObj} {L_B : B ⥤ LBObj} {L_C : C ⥤ LCObj} {L_D : D ⥤ LDObj}
  {RP : LAObj ⥤ LBObj} {RUC : LBObj ⥤ LCObj}
  {RUD : LAObj ⥤ LDObj} {RQ : LDObj ⥤ LCObj}

/- An underived square isomorphism can be transported through the two right-derived units and
the derived model of the composite.  The composite model is the only one that needs a universal
property, so intermediate derived functors remain freely reusable. -/

/-- The right-derived comparison induced by an underived square isomorphism. -/
@[stacks 05T2 "right-derived square from an underived isomorphism"]
noncomputable def squareOfIso
    (S : MorphismProperty A)
    (e : P ⋙ UC ≅ UD ⋙ Q)
    (αP : P ⋙ L_B ⟶ L_A ⋙ RP)
    (αUC : UC ⋙ L_C ⟶ L_B ⋙ RUC)
    (αUD : UD ⋙ L_D ⟶ L_A ⋙ RUD)
    (αQ : Q ⋙ L_C ⟶ L_D ⋙ RQ)
    [L_A.IsLocalization S]
    [hαGF : (RP ⋙ RUC).IsRightDerivedFunctor
      ((associator UD Q L_C).inv ≫ Functor.whiskerRight e.inv L_C ≫
        (associator P UC L_C).hom ≫
        iteratedUnit (F := P) (G := UC ⋙ L_C) (L := L_A) (L' := L_B)
          (RF := RP) (RG := RUC) αP αUC) S] :
    RP ⋙ RUC ⟶ RUD ⋙ RQ :=
  comparisonOfModels (F := UD) (G := Q ⋙ L_C) (L := L_A) (L' := L_D)
    (RF := RUD) (RG := RQ) (RGF := RP ⋙ RUC) S αUD αQ
    ((associator UD Q L_C).inv ≫ Functor.whiskerRight e.inv L_C ≫
      (associator P UC L_C).hom ≫
      iteratedUnit (F := P) (G := UC ⋙ L_C) (L := L_A) (L' := L_B)
        (RF := RP) (RG := RUC) αP αUC)

end Functor.RightDerived.Composition

end CategoryTheory
