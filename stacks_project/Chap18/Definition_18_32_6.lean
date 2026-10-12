/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard
import StacksCheckRecall

/-!
# Definition 18.32.6

The source-facing entry checks the ringed-site specialization of the generic Picard-group owner.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/- Definition 18.32.6 (040C): the Picard group of `(C, 𝒪)` is the commutative group of
isomorphism classes of invertible `𝒪`-modules under tensor product. -/
@[stacks 040C]
#check (PicardGroup J 𝒪 : Type _)

#check (inferInstance : AddCommGroup (PicardGroup J 𝒪))

end SheafOfModules.RingedSite
