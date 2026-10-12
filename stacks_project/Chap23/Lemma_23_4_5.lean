/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.AdicCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

section Surjective

variable {R : Type u} [CommRing R]
variable (J I : Ideal R) (n : ℕ) (h : J ^ n ≤ I)

/- Lemma 23.4.5 (tag `07KD`) (1): principal-adic completion surjects onto the quotient. -/
@[stacks 07KD "(1)"]
#check (AdicCompletion.toQuotient_surjective J I n h :
  Function.Surjective (AdicCompletion.toQuotient J I n h))

end Surjective

section Kernel

variable {R : Type u} [CommRing R]
variable (r : R) (I : Ideal R) (n : ℕ) (h : Ideal.span {r} ^ n ≤ I)
variable {x : AdicCompletion (Ideal.span {r}) R}

/- Lemma 23.4.5 (tag `07KD`) (2): the kernel is the image of the completion of `I`. -/
@[stacks 07KD "(2)"]
#check (AdicCompletion.Principal.mem_ker_toQuotient_iff r I n h :
  x ∈ RingHom.ker (AdicCompletion.toQuotient (Ideal.span {r}) I n h) ↔
    ∃ y : AdicCompletion (Ideal.span {r}) I,
      AdicCompletion.map (Ideal.span {r}) I.subtype y = x)

end Kernel

section Continuity

variable {R : Type u} [CommRing R] {I : Ideal R}
variable (gamma : DividedPowers I) (r : R) (n e : ℕ)
variable {x y : R} (hx : x ∈ I) (hy : y ∈ I)
variable (hxy : x - y ∈ Ideal.span {r} ^ e * I)

/- Lemma 23.4.5 (tag `07KD`) (3): divided powers are principal-adically continuous. -/
@[stacks 07KD "(3), continuity"]
#check (DividedPowers.dpow_sub_mem_principalPow_mul gamma r n e hx hy hxy :
  gamma.dpow n x - gamma.dpow n y ∈ Ideal.span {r} ^ e * I)

end Continuity

section UniqueExtension

variable {R : Type u} [CommRing R] {I : Ideal R}
variable (gamma : DividedPowers I) (r : R) (n : ℕ)
variable (h : Ideal.span {r} ^ n ≤ I)

/- Lemma 23.4.5 (tag `07KD`) (3): the compatible divided powers on the completion exist
uniquely. -/
@[stacks 07KD "(3), unique compatible extension"]
#check (DividedPowers.existsUnique_principalCompletionExtension gamma r n h :
  ∃! gammaHat : DividedPowers
      (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {r}) I n h)),
      gamma.IsDPMorphism gammaHat
      (algebraMap R (AdicCompletion (Ideal.span {r}) R)))

end UniqueExtension

section EventualStability

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable (gamma : DividedPowers I) (p : ℕ) [Fact p.Prime]
variable [Algebra (Int.LocalizationAtPrime p) R]
variable (n : ℕ) (h : Ideal.span {(p : R)} ^ n ≤ I)

/- Lemma 23.4.5 (tag `07KD`), moreover: high `p`-powers are eventually stable. -/
@[stacks 07KD "moreover, eventual stability"]
#check (DividedPowers.eventually_stable_primePowers gamma p n h :
  ∃ offset : ℕ,
    Ideal.span {(p : R)} ^ offset ≤ I ∧
      gamma.IsStableUnderPowers (Ideal.span {(p : R)}) offset)

end EventualStability

section Limit

variable {R : Type u} [CommRing R] {I : Ideal R}
variable (gamma : DividedPowers I) (J : Ideal R) (offset : ℕ)
variable (hstable : gamma.IsStableUnderPowers J offset)
variable (hpow : J ^ offset ≤ I)
variable (gammaHat : DividedPowers
  (RingHom.ker (AdicCompletion.toQuotient J I offset hpow)))
variable (hgammaHat : gamma.IsDPMorphism gammaHat
  (algebraMap R (AdicCompletion J R)))

/- Lemma 23.4.5 (tag `07KD`), moreover: the `p`-adic completion is the limit of the stable
quotient tower in divided power rings. -/
@[stacks 07KD "moreover, divided-power limit"]
#check (DividedPowers.QuotientPowerTower.isLimit
    gamma J offset hstable hpow gammaHat hgammaHat :
  IsLimit (DividedPowers.QuotientPowerTower.cone
    gamma J offset hstable hpow gammaHat hgammaHat))

end Limit

#check @AdicCompletion.toQuotient
#check @DividedPowers.exists_principalCompletionExtension
#check @DividedPowers.principalCompletionExtension_unique
#check @DividedPowers.IsStableUnderPowers
#check @DividedPowers.QuotientPowerTower.diagram
#check @DividedPowers.QuotientPowerTower.eval_isDPMorphism
#check @DividedPowers.QuotientPowerTower.cone
#check @DividedPowers.QuotientPowerTower.cone_π_app
#check @DividedPowers.QuotientPowerTower.lift
#check @DividedPowers.QuotientPowerTower.isLimit
