module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Presentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of globally presented module sheaves

This file records the source-independent preservation of freeness, global generation, and global
presentations by a pullback of module sheaves.  The concrete transported generators and
presentations reuse Mathlib's `GeneratingSections.map` and `Presentation.map`; the only additional
input is that the pullback carries the unit module to the unit module.
-/

@[expose] public section

open CategoryTheory Limits

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

/-- The pullback of a free module sheaf is canonically free on the same indexing type whenever
the pullback comparison on unit modules is invertible. -/
@[stacks 03DF "free comparison"]
noncomputable def pullbackFreeIso [IsIso (pullbackObjUnitToUnit f)] (I : Type u) :
    (pullback f).obj (free I : SheafOfModules S) ≅ (free I : SheafOfModules R) :=
  (mapFreeIso (pullback f) I (asIso (pullbackObjUnitToUnit f)).symm).symm

/-- A family of global generators transported through pullback. -/
@[stacks 03DF "transported generators"]
noncomputable def GeneratingSections.pullback
    [IsIso (pullbackObjUnitToUnit f)] {ℱ : SheafOfModules S}
    (σ : ℱ.GeneratingSections) :
    ((pullback f).obj ℱ).GeneratingSections :=
  σ.map (SheafOfModules.pullback f) (asIso (pullbackObjUnitToUnit f)).symm

section Presentation

variable [HasSheafify J AddCommGrpCat.{u}]

/-- A global presentation transported through pullback using Mathlib's functorial presentation
construction.  The stronger source-side `HasSheafify` hypothesis is needed by that concrete
construction; the preservation predicates below retain the weaker source hypotheses. -/
@[stacks 03DF "transported presentation"]
noncomputable def Presentation.pullback
    [IsIso (pullbackObjUnitToUnit f)] {ℱ : SheafOfModules S} (P : ℱ.Presentation) :
    ((SheafOfModules.pullback f).obj ℱ).Presentation :=
  P.map (SheafOfModules.pullback f) (asIso (pullbackObjUnitToUnit f)).symm

/-- Pullback preserves finiteness of the concrete transported global presentation. -/
@[stacks 03DF "finite transported presentation"]
instance Presentation.pullback_isFinite
    [IsIso (pullbackObjUnitToUnit f)] {ℱ : SheafOfModules S}
    (P : ℱ.Presentation) [P.IsFinite] :
    (P.pullback f).IsFinite := sorry

end Presentation

/-- Lemma 18.17.2 (1): pullback preserves free module sheaves. -/
@[stacks 03DF "(1)"]
instance pullback_isFree [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [IsFree ℱ] :
    IsFree ((pullback f).obj ℱ) := sorry

/-- Lemma 18.17.2 (2): pullback preserves finite free module sheaves. -/
@[stacks 03DF "(2)"]
instance pullback_isFiniteFree [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [IsFiniteFree ℱ] :
    IsFiniteFree ((pullback f).obj ℱ) := sorry

/-- Lemma 18.17.2 (3): pullback preserves global generation. -/
@[stacks 03DF "(3)"]
instance pullback_isGloballyGenerated [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [IsGloballyGenerated ℱ] :
    IsGloballyGenerated ((pullback f).obj ℱ) := sorry

/-- Lemma 18.17.2 (4): pullback preserves generation by a fixed number of global sections. -/
@[stacks 03DF "(4)"]
instance pullback_isGeneratedBy [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) (r : ℕ) [IsGeneratedBy ℱ r] :
    IsGeneratedBy ((pullback f).obj ℱ) r := sorry

/-- Lemma 18.17.2 (5): pullback preserves finite global generation. -/
@[stacks 03DF "(5)"]
instance pullback_isFiniteGloballyGenerated [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [IsFiniteGloballyGenerated ℱ] :
    IsFiniteGloballyGenerated ((pullback f).obj ℱ) := sorry

/-- Lemma 18.17.2 (6): pullback preserves the existence of a global presentation. -/
@[stacks 03DF "(6)"]
instance pullback_hasGlobalPresentation [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [HasGlobalPresentation ℱ] :
    HasGlobalPresentation ((pullback f).obj ℱ) := sorry

/-- Lemma 18.17.2 (7): pullback preserves the existence of a finite global presentation. -/
@[stacks 03DF "(7)"]
instance pullback_hasFiniteGlobalPresentation [IsIso (pullbackObjUnitToUnit f)]
    (ℱ : SheafOfModules S) [HasFiniteGlobalPresentation ℱ] :
    HasFiniteGlobalPresentation ((pullback f).obj ℱ) := sorry

end SheafOfModules
