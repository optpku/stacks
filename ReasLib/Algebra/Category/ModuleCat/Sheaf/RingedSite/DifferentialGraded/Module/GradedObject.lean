/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}} {𝒜 : DGA(𝒪)}

/-- The underlying integer-graded object of a differential graded module sheaf retains
every homogeneous component of its cochain complex. -/
def toGradedObject (M : DifferentialGradedModule 𝒜) :
    GradedObject ℤ (ringedSiteModuleCategory.{u, v, w, w} J 𝒪) :=
  M.toComplex.X

/-- Evaluation of the underlying graded object recovers the corresponding homogeneous part. -/
@[simp]
theorem toGradedObject_apply (M : DifferentialGradedModule 𝒜) (n : ℤ) :
    M.toGradedObject n = M.toComplex.X n := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule
