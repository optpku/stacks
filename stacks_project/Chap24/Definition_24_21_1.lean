/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.DifferentialGraded
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [CategoryTheory.Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {𝒜 : DGA(𝒪)} {L M : Mod(𝒜, d)}
variable (f g : Hom L M)

/- Definition 24.21.1: two differential graded module maps are homotopic when their closed
degree-zero presentations differ by the differential of a degree-`-1` homogeneous
`𝒜`-linear map. This is the canonical DG-category relation `DifferentialGradedCategory.Homotopic`. -/
@[stacks 0FS0] #check
  DifferentialGradedCategory.Homotopic L M
    (homToCompHom f) (homToCompHom g)

end

end SheafOfModules.RingedSite.DifferentialGradedModule
