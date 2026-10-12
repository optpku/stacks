/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.TestFamily.Acyclic
import StacksCheckRecall

/-!
# Lemma 24.25.6

The set-sized family and its two defining properties are carried by one neutral data owner.
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

/- Lemma 24.25.6 (tag 0FST): a set-sized family of acyclic DG `𝒜`-modules detects every
nonzero acyclic DG `𝒜`-module by a monomorphism from one family member. -/
@[stacks 0FST] #check Module.KInjective.AcyclicTestFamily 𝒜
#check Module.KInjective.AcyclicTestFamily.nonempty 𝒜

end


end SheafOfModules.RingedSite.DifferentialGradedModule
