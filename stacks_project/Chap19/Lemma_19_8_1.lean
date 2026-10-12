/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.AbelianDual.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

open SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{max u v z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

variable (𝒥 : Sheaf J AddCommGrpCat.{max u v z}) [Injective 𝒥]

/- Lemma 19.8.1: `ℱ ↦ Hom_Ab(ℱ, 𝒥)`, with its `𝒪`-action by precomposition,
is exact for the injective abelian sheaf fixed in the preceding construction. -/
@[stacks 01DR] #check
  (AbelianDual.exact 𝒪 𝒥 :
    exactFunctor
      (ringedSiteModuleCategory.{u, v, max u v z, w} J 𝒪)ᵒᵖ
      (ringedSiteModuleCategory.{u, v, max u v z, w} J 𝒪)
      (AbelianDual.functor 𝒪 𝒥))
