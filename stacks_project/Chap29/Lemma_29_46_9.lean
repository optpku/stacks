/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.PrimePower

universe u

/- Lemma 29.46.9: for a prime `p` and a ring map inducing a bijection after localization away
from `p`, the affine spectrum map is a universal homeomorphism exactly when its kernel is locally
nilpotent and every target element satisfies the common prime-power range condition. -/
@[stacks 0CNF] #check
  (AlgebraicGeometry.UniversalHomeomorphism.specMap_iff_ker_isLocallyNilpotent_and_primePowerRange :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (p : ℕ) (hp : Nat.Prime p)
      (f : A →+* B) (hlocal : Function.Bijective (Localization.awayMap f (p : A))),
      AlgebraicGeometry.UniversalHomeomorphism (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) ↔
        (RingHom.ker f).IsLocallyNilpotent ∧
          ∀ b : B, ∃ n : ℕ, p ^ n • b ∈ f.range ∧ b ^ (p ^ n) ∈ f.range)
