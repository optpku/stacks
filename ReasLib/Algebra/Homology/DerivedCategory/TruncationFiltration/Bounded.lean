module

public import ReasLib.Algebra.Homology.DerivedCategory.TruncationFiltration
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.Filtration.Complex.Cochain
public import ReasLib.CategoryTheory.Filtration.Complex.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stage control for bounded truncation filtrations

For a bounded derived module, sufficiently high stages of the canonical upper-truncation
filtration are acyclic, while sufficiently low stage inclusions are quasi-isomorphisms.

@stack 0H7Z
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped ZeroObject

universe u

-- Local instance justification (instance diamond): use the standard derived localization for
-- module categories in this bounded specialization.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory.TruncationFilteredPreimage

variable {R : Type u} [CommRing R]
variable [LocallySmall.{0} (ModuleCat R)] [WellPowered.{0} (ModuleCat R)]
  [HasWidePullbacks (ModuleCat R)] [HasCoproducts (ModuleCat R)]
  [InitialMonoClass (ModuleCat R)]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)

/-- For sufficiently high indices, the truncation-filtration stage of a bounded derived module
is acyclic. -/
@[stacks 0H7Z "eventual acyclicity of the bounded truncation filtration"]
theorem eventuallyAcyclic (K : DbMod) :
    ∃ p0 : ℤ, ∀ ⦃p : ℤ⦄, p0 ≤ p →
      ((truncationFilteredPreimage K.obj).stage p).Acyclic := sorry

/-- For sufficiently low indices, the stage inclusion of the truncation filtration of a bounded
derived module is a quasi-isomorphism. -/
@[stacks 0H7Z "eventual quasi-isomorphism of bounded truncation stages"]
theorem eventuallyQuasiIsoStageInclusion (K : DbMod) :
    ∃ p1 : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p1 →
      QuasiIso ((truncationFilteredPreimage K.obj).stageInclusion p) := sorry

/-- The two eventual stage-control properties of the truncation filtration of a bounded derived
module. -/
@[stacks 0H7Z "bounded truncation-filtration stage control"]
theorem stageControl (K : DbMod) :
    (∃ p0 : ℤ, ∀ ⦃p : ℤ⦄, p0 ≤ p →
      ((truncationFilteredPreimage K.obj).stage p).Acyclic) ∧
    (∃ p1 : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p1 →
      QuasiIso ((truncationFilteredPreimage K.obj).stageInclusion p)) := sorry

end CategoryTheory.DerivedCategory.TruncationFilteredPreimage
