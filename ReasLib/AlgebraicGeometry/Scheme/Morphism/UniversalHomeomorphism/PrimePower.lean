/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

@[expose] public section

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B]

/-- Let `p` be prime and let `f : A →+* B` induce a bijection after localization away from `p`.
The affine spectrum map of `f` is a universal homeomorphism exactly when its kernel is locally
nilpotent and every target element has a common `p`-power whose multiple and power lie in the
range of `f`. -/
theorem specMap_iff_ker_isLocallyNilpotent_and_primePowerRange
    (p : ℕ) (hp : Nat.Prime p) (f : A →+* B)
    (hlocal : Function.Bijective (Localization.awayMap f (p : A))) :
    AlgebraicGeometry.UniversalHomeomorphism (Spec.map (CommRingCat.ofHom f)) ↔
      (RingHom.ker f).IsLocallyNilpotent ∧
        ∀ b : B, ∃ n : ℕ, p ^ n • b ∈ f.range ∧ b ^ (p ^ n) ∈ f.range := sorry

end AlgebraicGeometry.UniversalHomeomorphism
