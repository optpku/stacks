/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {𝒪 : Sheaf J CommRingCat.{u}}

variable (𝒥 : Sheaf J AddCommGrpCat.{u}) [Injective 𝒥]
variable (ℱ : ringedSiteModuleCategory.{u, u, u, u} J 𝒪)

/- Lemma 19.8.3: the canonical object
`J(ℱ) = (FreeFlatCover(ℱ^∨))^∨` is injective for every module sheaf `ℱ`. -/
@[stacks 01DT] #check
  (AbelianDual.Resolution.obj_injective 𝒪 𝒥 ℱ :
    Injective (AbelianDual.Resolution.obj 𝒪 𝒥 ℱ))

#check @FreeFlatCover.functor
#check @FreeFlatCover.π
#check @AbelianDual.Resolution.ι
