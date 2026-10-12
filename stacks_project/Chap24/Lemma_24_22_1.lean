/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Shift
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable (𝒜 : DGA(𝒪))

/- Lemma 24.22.1 (1): axiom `(A)` for `Mod(𝒜, d)` is exposed through the canonical
`Abelian` interface. In particular, binary direct sums are the category-theoretic biproducts,
and their structure maps are ordinary DG-module maps, hence closed homogeneous maps of degree
zero under the canonical DG enrichment. -/
@[stacks 0FS4] #check
  (instAbelian 𝒜 : Abelian (Mod(𝒜, d)))

/- Lemma 24.22.1 (2): the direct-sum consequence of axiom `(A)` is available to downstream
code through the standard `HasBinaryBiproducts` typeclass. -/
#check (inferInstance : HasBinaryBiproducts (Mod(𝒜, d)))

/- Lemma 24.22.1 (3): axiom `(B)` is the canonical coherent integer-shift structure on
`Mod(𝒜, d)`. -/
@[stacks 0FS4] #check
  (Shift.hasShift 𝒜 : HasShift (Mod(𝒜, d)) ℤ)

/- The abstract shift functor is identified with the explicit shifted DG-module construction. -/
#check Shift.shiftFunctor_eq 𝒜

end


end SheafOfModules.RingedSite.DifferentialGradedModule
