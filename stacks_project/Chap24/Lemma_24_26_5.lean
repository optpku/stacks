/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Kernel
import StacksCheckRecall

/-!
# Lemma 24.26.5

The kernel of the canonical Verdier localization is computed by the acyclic object property.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))

/- Lemma 24.26.5 (0FT6): the kernel of `Qh` is precisely the acyclic subcategory. -/
@[stacks 0FT6]
#check
  (DerivedCategory.Qh_kernel_eq 𝒜 :
    Functor.kernel (DerivedCategory.Qh 𝒜) = Homotopy.acyclic 𝒜)

end SheafOfModules.RingedSite.DifferentialGradedModule
