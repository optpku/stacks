/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of symmetric powers

Symmetric powers preserve the standard finiteness, freeness, and coherence properties of
module sheaves under the stated sheafification hypotheses.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (F : ringedSiteModuleCategory J 𝒪) (n : ℕ)

section OneLevel

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Symmetric powers preserve local generation by sections. -/
@[stacks 01CK "(1), symmetric power"]
theorem isLocallyGeneratedBySections
    [IsLocallyGeneratedBySections F] :
    IsLocallyGeneratedBySections (sheaf 𝒪 F n) := sorry

/-- Symmetric powers preserve finite type. -/
@[stacks 01CK "(2), symmetric power"]
theorem isFiniteType [F.IsFiniteType] : (sheaf 𝒪 F n).IsFiniteType := sorry

/-- Symmetric powers preserve finite presentation. -/
@[stacks 01CK "(3), symmetric power"]
theorem isFinitePresentation [F.IsFinitePresentation] :
    (sheaf 𝒪 F n).IsFinitePresentation := sorry

/-- Symmetric powers preserve quasi-coherence. -/
@[stacks 01CK "(5), symmetric power"]
theorem isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F n).IsQuasicoherent := sorry

/-- Symmetric powers preserve local freeness. -/
@[stacks 01CK "(6), symmetric power"]
theorem isLocallyFree [F.IsLocallyFree] : (sheaf 𝒪 F n).IsLocallyFree := sorry

/-- Symmetric powers preserve finite local freeness. -/
@[stacks 01CK "finite locally free symmetric power"]
theorem isFiniteLocallyFree [F.IsFiniteLocallyFree] :
    IsFiniteLocallyFree (sheaf 𝒪 F n) := sorry

/-- The `n`th symmetric power of a finite locally free module sheaf of rank `r` is finite locally
free of rank `Nat.multichoose r n`. -/
@[stacks 01CK "symmetric power rank formula"]
theorem isFiniteLocallyFreeOfRank (r : ℕ) [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFreeOfRank (Nat.multichoose r n) (sheaf 𝒪 F n) := sorry

end OneLevel

section Iterated

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Every positive symmetric power of a coherent module sheaf is coherent. -/
@[stacks 01CK "(4), symmetric power"]
theorem isCoherent_succ [IsCoherent F] :
    IsCoherent (sheaf 𝒪 F (n + 1)) := sorry

end Iterated

end SheafOfModules.RingedSite.SymmetricPower
