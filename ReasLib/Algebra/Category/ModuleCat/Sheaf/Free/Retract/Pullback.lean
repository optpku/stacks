module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract

/-!
# Pullback of retracts of finite free module sheaves

Pullback preserves the retract closure of finite free module sheaves whenever the underlying
site functor is final. The result is stated as an inequality into an inverse-image property so it
can feed generic termwise functoriality results directly.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace SheafOfModules

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
variable [(pushforward f).IsRightAdjoint]

/-- Pullback sends every retract of a finite free module sheaf to a retract of a finite free
module sheaf. -/
theorem finiteFreeRetractModuleProperty_pullback :
    finiteFreeRetractModuleProperty S ≤
      (finiteFreeRetractModuleProperty R).inverseImage (pullback f) := sorry

end SheafOfModules
