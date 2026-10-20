import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule.Endomorphism
import StacksCheckRecall

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 𝒝 : DGA(𝒪)) (N : Mod(𝒝, d))

/- Lemma 24.17.2: differential graded `(𝒜, 𝒝)`-bimodule structures on the fixed right
`𝒝`-module `N` are equivalent to degreewise presentations of differential graded algebra maps
from `𝒜` to the right-`𝒝`-linear endomorphisms of `N`. -/
@[stacks 0FRR] #check
  (FixedRight.actionEquiv 𝒜 𝒝 N : FixedRight 𝒜 𝒝 N ≃ ActionOn 𝒜 N)

end


end SheafOfModules.RingedSite.DifferentialGradedBimodule
