module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Theorem 24.25.13 (tag 0FT0): DG module sheaves admit functorial quasi-isomorphic
replacements which are both K-injective and graded injective. -/
@[stacks 0FT0] #check Module.KInjective.ResolutionFunctor 𝒜
#check Module.KInjective.ResolutionFunctor.nonempty 𝒜

end


end SheafOfModules.RingedSite.DifferentialGradedModule
