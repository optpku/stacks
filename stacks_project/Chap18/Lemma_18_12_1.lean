module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import StacksCheckRecall

/-!
# Lemma 18.12.1

The direct-image module structure and its functoriality are carried by Mathlib's
`SheafOfModules.pushforward`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
variable (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
variable (F : D ⥤ C) [Functor.IsContinuous F JD JC]
variable (𝒪 : Sheaf JC RingCat.{u})

/- Lemma 18.12.1 (03D1): direct image sends an `𝒪`-module to a module over the
direct-image ring sheaf, functorially. -/
@[stacks 03D1]
#check
  (SheafOfModules.pushforward
      (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪)) :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((F.sheafPushforwardContinuous RingCat.{u} JD JC).obj 𝒪))
