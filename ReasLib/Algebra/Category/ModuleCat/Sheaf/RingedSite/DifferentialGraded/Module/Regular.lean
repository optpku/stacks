/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module

/-!
# The regular module of a differential graded algebra sheaf

A differential graded algebra acts on itself on the right.  This deterministic data owner is
the canonical representing object used by mapping-cone and hypercohomology constructions.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

namespace DifferentialGradedAlgebra

/-- A differential graded algebra sheaf acts on its regular right differential graded module
by multiplication. -/
@[reducible]
def regularModule (𝒜 : DGA(𝒪)) : Mod(𝒜, d) :=
  SheafOfModules.RingedSite.DifferentialGradedModule.regular 𝒜

/-- The underlying cochain complex of the regular module is the algebra itself. -/
theorem regularModule_toComplex (𝒜 : DGA(𝒪)) :
    𝒜.regularModule.toComplex = 𝒜.toComplex := sorry

/-- The right action of the regular module is multiplication in the algebra. -/
theorem regularModule_smul (𝒜 : DGA(𝒪)) (n m : ℤ) :
    𝒜.regularModule.smul n m = 𝒜.mul n m := sorry

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
