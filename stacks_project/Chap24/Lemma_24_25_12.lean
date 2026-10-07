module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Enlargement.TestFamily
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

/- Lemma 24.25.12 (tag 0FSZ): every set-indexed family of monomorphisms between acyclic DG
modules admits a functorial monomorphic quasi-isomorphic enlargement solving all associated
extension problems. -/
@[stacks 0FSZ] #check Module.KInjective.AcyclicEnlargement 𝒜
#check Module.KInjective.AcyclicEnlargement.nonempty 𝒜
#check Module.KInjective.TestFamily.nonempty_enlargement

end


end SheafOfModules.RingedSite.DifferentialGradedModule
