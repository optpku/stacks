module

import StacksCheckRecall
import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.AdicCompletion

@[expose] public section

open CategoryTheory

universe u

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) {J : Ideal B} (δ : DividedPowers J) (p : ℕ)
variable [Fact (Nat.Prime p)] [Algebra (Int.LocalizationAtPrime p) A]
variable (h_nilpotent : IsNilpotent (p : B ⧸ J))

/- Lemma 60.6.10 (1): the stage-limit comparison is an isomorphism. -/
@[stacks 07KK] #check (DividedPowerDifferential.originalLimitComparison_isIso f δ p h_nilpotent :
  IsIso (DividedPowerDifferential.originalLimitComparison f δ p h_nilpotent))

/- Lemma 60.6.10 (2): the completion-limit comparison is an isomorphism. -/
@[stacks 07KK] #check (DividedPowerDifferential.completionLimitComparison_isIso f δ p h_nilpotent :
  IsIso (DividedPowerDifferential.completionLimitComparison f δ p h_nilpotent))
