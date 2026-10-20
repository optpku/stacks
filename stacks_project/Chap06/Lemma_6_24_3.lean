module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Presheaf TopCat TopCat.Presheaf

noncomputable section

universe u

section

/- The site-generic module adjunction is the reusable mathlib owner, including for modules over
possibly noncommutative ring presheaves and for changes of sites. -/
recall PresheafOfModules.pullbackPushforwardAdjunction

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Presheaf CommRingCat.{u})
variable (𝒢 : PMod(ringPresheafOfComm 𝒪))
variable (ℱ : PMod(ringPresheafOfComm ((pullback CommRingCat f).obj 𝒪)))

/- Lemma 6.24.3: under the Stacks convention that rings are commutative with `1`, inverse image of
presheaves of modules along `f` is left adjoint to direct image. -/
@[stacks 008U "adjunction between inverse and direct image of presheaves of modules"]
#check
  ((PresheafOfModules.pullbackPushforwardAdjunction
      (commRingPresheafPullbackUnit f 𝒪)).homEquiv 𝒢 ℱ :
    ((PresheafOfModules.pullback (commRingPresheafPullbackUnit f 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (PresheafOfModules.pushforward
        (commRingPresheafPullbackUnit f 𝒪)).obj ℱ))

end
