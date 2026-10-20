module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCheckRecall

/-!
# Lemma 18.12.3

The textbook Hom-set bijection is the Hom equivalence of Mathlib's pullback-pushforward
adjunction for module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable [HasWeakSheafify JC RingCat.{u}]
variable [HasWeakSheafify JC AddCommGrpCat.{u}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf JD RingCat.{u})
variable (𝒢 : SheafOfModules 𝒪)
variable (ℱ : SheafOfModules ((F.sheafPullback RingCat.{u} JD JC).obj 𝒪))

/- Lemma 18.12.3 (03D3): pullback and pushforward induce the canonical Hom equivalence
between modules over `𝒪` and modules over its inverse image. -/
@[stacks 03D3]
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      ((F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        ((F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        ((F.sheafAdjunctionContinuous RingCat.{u} JD JC).unit.app 𝒪)).obj ℱ))
