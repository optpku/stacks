/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

namespace TopCat.Presheaf

universe u

variable {X : TopCat.{u}}

section CommRing

variable {𝒪₁ 𝒪₂ : X.Presheaf CommRingCat.{u}} (p : 𝒪₁ ⟶ 𝒪₂)
variable
  (𝒢 : PresheafOfModules (ringPresheafOfComm 𝒪₁))
  (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪₂))

/- Lemma 6.6.2: under the Stacks convention that rings are commutative with `1`, change of rings
for presheaves of modules is left adjoint to restriction of scalars. -/
@[stacks 006R "change of rings is left adjoint to restriction of scalars"]
#check PresheafOfModules.pullbackPushforwardAdjunction (commRingPresheafHomOverId p)

/- The source's canonical bijection is the inverse hom-equivalence of this adjunction. -/
#check
  (((PresheafOfModules.pullbackPushforwardAdjunction
      (commRingPresheafHomOverId p)).homEquiv 𝒢 ℱ).symm :
    (𝒢 ⟶ (PresheafOfModules.pushforward (commRingPresheafHomOverId p)).obj ℱ) ≃
      ((PresheafOfModules.pullback (commRingPresheafHomOverId p)).obj 𝒢 ⟶ ℱ))

end CommRing

end TopCat.Presheaf
