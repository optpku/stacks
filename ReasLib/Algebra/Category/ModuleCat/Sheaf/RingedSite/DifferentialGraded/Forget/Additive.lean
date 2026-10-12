/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Forget
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule.Preadditive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Preadditive

/-!
# Additivity of forgetting the differential

This leaf records the additive bridge between differential graded modules and the matching
tensor-morphism presentation of graded modules.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedModule

/-- Forgetting the differential of a differential graded module is additive. -/
instance forgetToGraded_additive (𝒜 : DGA(𝒪)) :
    (forgetToGraded 𝒜).Additive := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
