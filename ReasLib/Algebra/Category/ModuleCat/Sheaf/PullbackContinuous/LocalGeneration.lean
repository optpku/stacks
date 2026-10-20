module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalGeneration

/-!
# Pullback of Locally Generated Sheaves of Modules

The canonical inverse-image functor associated to a continuous final functor preserves local
generation and finite type over arbitrary sheaves of rings.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ v₁ u₂ v₂ w

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : D ⥤ C} [F.IsContinuous K J]
variable {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : D, HasWeakSheafify (K.over U) AddCommGrpCat.{w}]
variable [∀ U : D, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} K J).obj R)
variable [(SheafOfModules.pushforward f).IsRightAdjoint]

/-- Inverse image preserves local generation by sections. -/
@[stacks 03DO "(3)", stacks 01B3]
instance pullback_isLocallyGeneratedBySections
    [F.Final] (M : SheafOfModules.{w} S)
    [SheafOfModules.IsLocallyGeneratedBySections M] :
    SheafOfModules.IsLocallyGeneratedBySections ((SheafOfModules.pullback f).obj M) := sorry

/-- Inverse image preserves local generation by a fixed number of sections. -/
@[stacks 03DO "(4)"]
instance pullback_isLocallyGeneratedBy
    [F.Final] (M : SheafOfModules.{w} S) (r : ℕ)
    [SheafOfModules.IsLocallyGeneratedBy M r] :
    SheafOfModules.IsLocallyGeneratedBy ((SheafOfModules.pullback f).obj M) r := sorry

/-- Inverse image preserves finite type. -/
@[stacks 03DO "(5)", stacks 01B6]
instance pullback_isFiniteType
    [F.Final] (M : SheafOfModules.{w} S) [M.IsFiniteType] :
    ((SheafOfModules.pullback f).obj M).IsFiniteType := sorry

end SheafOfModules
