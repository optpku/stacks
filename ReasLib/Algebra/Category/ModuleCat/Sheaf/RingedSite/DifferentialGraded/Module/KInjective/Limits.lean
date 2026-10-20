/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic

/-!
# Limits of K-injective differential graded modules

Products of represented DG modules are computed before passage to the homotopy category, so
the intrinsic product closure of K-injective objects gives a module-level typeclass instance.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped ZeroObject
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Product closure is transported through the pinned homotopy structure.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module.IsKInjective

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)}

/-- The zero DG module is K-injective. -/
instance zero : IsKInjective (0 : Mod(𝒜, d)) := sorry

/-- A product of K-injective DG modules is K-injective. -/
@[stacks 0FSV]
instance product {ι : Type w} (I : ι → Mod(𝒜, d))
    [HasProduct I] [∀ i, IsKInjective (I i)] :
    IsKInjective (∏ᶜ I) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Module.IsKInjective
