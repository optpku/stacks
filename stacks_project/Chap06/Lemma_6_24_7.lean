/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopCat TopCat.Sheaf

noncomputable section

universe u

section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (𝒪 : TopCat.Sheaf CommRingCat.{u} Y)
variable (𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm.{u, u} 𝒪))
variable
  (ℱ : SheafOfModules
    (TopCat.Sheaf.ringSheafOfComm.{u, u} ((pullback CommRingCat.{u} f).obj 𝒪)))

/- The generic `SheafOfModules.pullbackPushforwardAdjunction` is the canonical owner, and its
specialized `homEquiv` is exactly the source morphism-set bijection. Keeping only this derived view
avoids a local wrapper and does not tag the stronger site-generic adjunction as the source lemma. -/
/- Lemma 6.24.7: under the Stacks convention that rings are commutative with `1`, morphisms from
the inverse image of `𝒢` to `ℱ` correspond canonically to morphisms from `𝒢` to the direct image
of `ℱ`, restricted along `𝒪 ⟶ f_* f⁻¹𝒪`. -/
@[stacks 008Y "adjunction bijection for inverse and direct images of module sheaves"]
#check
  (((SheafOfModules.pullbackPushforwardAdjunction
      (commRingSheafPullbackUnit f 𝒪)).homEquiv 𝒢 ℱ) :
    ((SheafOfModules.pullback
        (commRingSheafPullbackUnit f 𝒪)).obj 𝒢 ⟶ ℱ) ≃
      (𝒢 ⟶ (SheafOfModules.pushforward
        (commRingSheafPullbackUnit f 𝒪)).obj ℱ))

end
