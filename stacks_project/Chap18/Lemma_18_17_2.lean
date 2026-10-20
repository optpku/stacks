/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Pullback
import StacksCheckRecall

/-!
# Lemma 18.17.2

Compatibility facade for preservation of free, globally generated, and globally presented module
sheaves under pullback.  Concrete generators and presentations are transported by Mathlib's
`GeneratingSections.map` and `Presentation.map` in the shared owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ u

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} [F.IsContinuous J K]
variable {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify K AddCommGrpCat.{u}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (f : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
variable [(pushforward f).IsRightAdjoint]
variable [IsIso (pullbackObjUnitToUnit f)]
variable (ℱ : SheafOfModules S)

section Free

variable [IsFree ℱ]

/- Lemma 18.17.2 (1): pullback preserves freeness. -/
@[stacks 03DF "(1)"]
#check (pullback_isFree f ℱ : IsFree ((pullback f).obj ℱ))

end Free

section FiniteFree

variable [IsFiniteFree ℱ]

/- Lemma 18.17.2 (2): pullback preserves finite freeness. -/
@[stacks 03DF "(2)"]
#check (pullback_isFiniteFree f ℱ : IsFiniteFree ((pullback f).obj ℱ))

end FiniteFree

section GloballyGenerated

variable [IsGloballyGenerated ℱ]

/- Lemma 18.17.2 (3): pullback preserves global generation. -/
@[stacks 03DF "(3)"]
#check (pullback_isGloballyGenerated f ℱ : IsGloballyGenerated ((pullback f).obj ℱ))

end GloballyGenerated

section GeneratedBy

variable (r : ℕ) [IsGeneratedBy ℱ r]

/- Lemma 18.17.2 (4): pullback preserves generation by `r` global sections. -/
@[stacks 03DF "(4)"]
#check (pullback_isGeneratedBy f ℱ r : IsGeneratedBy ((pullback f).obj ℱ) r)

end GeneratedBy

section FiniteGeneration

variable [IsFiniteGloballyGenerated ℱ]

/- Lemma 18.17.2 (5): pullback preserves finite global generation. -/
@[stacks 03DF "(5)"]
#check (pullback_isFiniteGloballyGenerated f ℱ :
  IsFiniteGloballyGenerated ((pullback f).obj ℱ))

end FiniteGeneration

section Presentation

variable [HasGlobalPresentation ℱ]

/- Lemma 18.17.2 (6): pullback preserves the existence of a global presentation. -/
@[stacks 03DF "(6)"]
#check (pullback_hasGlobalPresentation f ℱ :
  HasGlobalPresentation ((pullback f).obj ℱ))

end Presentation

section FinitePresentation

variable [HasFiniteGlobalPresentation ℱ]

/- Lemma 18.17.2 (7): pullback preserves the existence of a finite global presentation. -/
@[stacks 03DF "(7)"]
#check (pullback_hasFiniteGlobalPresentation f ℱ :
  HasFiniteGlobalPresentation ((pullback f).obj ℱ))

end FinitePresentation

end SheafOfModules
