/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.13.2

The abelian, (co)complete, AB5, and forgetful-preservation infrastructure for differential
graded modules is owned by `DifferentialGraded.Limits`.
-/

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

/- Lemma 24.13.2 (0FRJ): differential graded modules have the expected abelian and pointwise
(co)limit structure, and forgetting the differential preserves it. -/
@[stacks 0FRJ]
#check @DifferentialGradedModule.instAbelian
#check @DifferentialGradedModule.instHasColimits
#check @DifferentialGradedModule.instAB5
#check @DifferentialGradedModule.instHasLimits
#check @DifferentialGradedModule.forgetToGradedPreservesLimits
#check @DifferentialGradedModule.forgetToGradedPreservesColimits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable (𝒜 : DGA(𝒪))

#synth Abelian (Mod(𝒜, d))
#synth HasCoproducts (Mod(𝒜, d))
#synth HasColimits (Mod(𝒜, d))
#synth AB5 (Mod(𝒜, d))
#synth HasProducts (Mod(𝒜, d))
#synth HasLimits (Mod(𝒜, d))
#synth PreservesLimits (DifferentialGradedModule.forgetToGraded 𝒜)
#synth PreservesColimits (DifferentialGradedModule.forgetToGraded 𝒜)

end

end SheafOfModules.RingedSite
