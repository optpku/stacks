module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise.Map

/-!
# Pullback of strictly perfect complexes of module sheaves

This file combines the generic functoriality of bounded termwise object properties with
pullback preservation of finite-free retracts.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace SheafOfModules.CochainComplex

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
variable {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify K AddCommGrpCat.{w}]
variable [HasWeakSheafify K AddCommGrpCat.{w}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable (f : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
variable [(SheafOfModules.pushforward f).IsRightAdjoint]

/-- Pullback along a final continuous site functor preserves strictly perfect complexes. -/
theorem IsStrictlyPerfect.pullback {E : CochainComplex (SheafOfModules S) ℤ}
    (hE : IsStrictlyPerfect (R := S) E) :
    IsStrictlyPerfect (R := R)
      (((SheafOfModules.pullback f).mapHomologicalComplex (up ℤ)).obj E) := sorry

end SheafOfModules.CochainComplex
