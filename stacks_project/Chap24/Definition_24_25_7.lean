/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
variable {𝒜 : DGA(𝒪)} (I : Mod(𝒜, d))

/- Definition 24.25.7 (tag 0FSU): a DG module is K-injective when every morphism to it from an
acyclic object vanishes in the intrinsic DG homotopy category. -/
@[stacks 0FSU] #check Module.IsKInjective I
#check Module.IsKInjective.iff I
#check Homotopy.KInjective.iff 𝒜 ((toK 𝒜).obj I)

end


end SheafOfModules.RingedSite.DifferentialGradedModule
