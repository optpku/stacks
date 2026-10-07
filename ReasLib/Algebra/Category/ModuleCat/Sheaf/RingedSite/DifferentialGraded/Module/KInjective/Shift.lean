module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Shift

/-!
# Shifts of K-injective differential graded modules

K-injectivity is stable under every integer shift.  This leaf exposes that closure directly at
the represented DG-module layer for typeclass-driven downstream arguments.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib intentionally keeps this construction non-global because a global instance breaks
-- sheaf/free elaboration.  Shift closure is stated in the same pinned homotopy triangulation.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module.IsKInjective

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)}

/-- Every integer shift of a K-injective DG module is K-injective. -/
noncomputable instance shift (I : Mod(𝒜, d)) [IsKInjective I] (n : ℤ) :
    IsKInjective
      ((CategoryTheory.shiftFunctor (Mod(𝒜, d)) n).obj I) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Module.IsKInjective
