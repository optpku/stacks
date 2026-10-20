module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf CommRingCat.{u} X)
variable
  (𝒢 : SheafOfModules
    (TopCat.Sheaf.ringSheafOfComm.{u, u} ((Sheaf.pushforward CommRingCat.{u} f).obj 𝒪)))
variable (ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm.{u, u} 𝒪))

/- The site-generic `SheafOfModules.pullbackPushforwardAdjunction` is the canonical owner.
Specializing its ring map to the identity of `f_* 𝒪` makes its left adjoint the source tensor
pullback `𝒪 ⊗_{f⁻¹ f_* 𝒪} f⁻¹ 𝒢`, while its right adjoint is the direct image of `ℱ`; the
specialized `homEquiv` therefore gives the source correspondence without a parallel wrapper. -/
/- Lemma 6.24.8: morphisms from the tensor pullback
`𝒪 ⊗_{f⁻¹ f_* 𝒪} f⁻¹ 𝒢` to `ℱ` correspond canonically to morphisms from `𝒢` to the direct image
`f_* ℱ`. -/
@[stacks 008Z "tensor pullback and direct image adjunction for module sheaves"]
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (commRingSheafPushforwardId f 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        (commRingSheafPushforwardId f 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        (commRingSheafPushforwardId f 𝒪)).obj ℱ))

end
