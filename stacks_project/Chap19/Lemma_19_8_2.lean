/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Evaluation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v w z

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

variable (𝒥 : Sheaf J AddCommGrpCat.{max u v z})
variable (h𝒥 : AbelianDual.Separates 𝒪 𝒥)
variable (ℱ : ringedSiteModuleCategory.{u, v, max u v z, w} J 𝒪)

/- Lemma 19.8.2: for every `𝒪`-module `ℱ`, local evaluation gives a monomorphism
`ℱ ⟶ Hom_Ab(Hom_Ab(ℱ, 𝒥), 𝒥)` whenever `𝒥` separates maps of `𝒪`-modules. -/
@[stacks 01DS] #check
  (AbelianDual.mono_toBidual 𝒪 𝒥 h𝒥 ℱ :
    Mono (AbelianDual.toBidual 𝒪 𝒥 ℱ))

#check @AbelianDual.mono_toBidual
