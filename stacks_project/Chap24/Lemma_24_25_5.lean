/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.TestFamily.GradedInjective
import StacksCheckRecall

/-!
# Lemma 24.25.5

The source statement is represented by the neutral explicit test-family owner rather than a
chapter-local class with four independent parameters.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Lemma 24.25.5: there is a set-indexed family of monomorphisms between acyclic DG
`𝒜`-modules whose right lifting condition detects injectivity after `forgetToGraded 𝒜`. -/
@[stacks 0FSS] #check Module.KInjective.GradedInjectiveTestFamily 𝒜
#check Module.KInjective.GradedInjectiveTestFamily.nonempty 𝒜

end


end SheafOfModules.RingedSite.DifferentialGradedModule
