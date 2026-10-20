module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of exterior powers

Exterior powers preserve the standard finiteness, freeness, and coherence properties of
module sheaves under the stated sheafification hypotheses.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (F : ringedSiteModuleCategory J 𝒪) (n : ℕ)

section OneLevel

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Exterior powers preserve local generation by sections. -/
@[stacks 01CK "(1), exterior power"]
theorem isLocallyGeneratedBySections
    [IsLocallyGeneratedBySections F] :
    IsLocallyGeneratedBySections (sheaf 𝒪 F n) := sorry

/-- Exterior powers preserve finite type. -/
@[stacks 01CK "(2), exterior power"]
theorem isFiniteType [F.IsFiniteType] : (sheaf 𝒪 F n).IsFiniteType := sorry

/-- Exterior powers preserve finite presentation. -/
@[stacks 01CK "(3), exterior power"]
theorem isFinitePresentation [F.IsFinitePresentation] :
    (sheaf 𝒪 F n).IsFinitePresentation := sorry

/-- Exterior powers preserve quasi-coherence. -/
@[stacks 01CK "(5), exterior power"]
theorem isQuasicoherent [F.IsQuasicoherent] :
    (sheaf 𝒪 F n).IsQuasicoherent := sorry

/-- Exterior powers preserve local freeness. -/
@[stacks 01CK "(6), exterior power"]
theorem isLocallyFree [F.IsLocallyFree] : (sheaf 𝒪 F n).IsLocallyFree := sorry

/-- Exterior powers preserve finite local freeness. -/
@[stacks 01CK "finite locally free exterior power"]
theorem isFiniteLocallyFree [F.IsFiniteLocallyFree] :
    IsFiniteLocallyFree (sheaf 𝒪 F n) := sorry

/-- The `n`th exterior power of a finite locally free module sheaf of rank `r` is finite
locally free of rank `Nat.choose r n`. -/
@[stacks 01CK "exterior power rank formula"]
instance isFiniteLocallyFreeOfRank (r : ℕ) [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFreeOfRank (Nat.choose r n) (sheaf 𝒪 F n) := sorry

/-- The top exterior power of a finite locally free module sheaf of rank `r` is finite locally
free of rank one. -/
@[stacks 0FJN "top exterior power"]
theorem top_rankOne (r : ℕ) [IsFiniteLocallyFreeOfRank r F] :
    IsFiniteLocallyFreeOfRank 1 (sheaf 𝒪 F r) := sorry

end OneLevel

section Iterated

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{max u v}]
variable [∀ (U : C) (V : Over U),
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Every positive exterior power of a coherent module sheaf is coherent. -/
@[stacks 01CK "(4), exterior power"]
theorem isCoherent_succ [IsCoherent F] :
    IsCoherent (sheaf 𝒪 F (n + 1)) := sorry

end Iterated

end SheafOfModules.RingedSite.ExteriorPower
