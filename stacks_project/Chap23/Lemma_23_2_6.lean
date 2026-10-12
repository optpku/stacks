/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

universe u

section

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable {I : Ideal A} (gamma : DividedPowers I)

/- Lemma 23.2.6 (07GR): under quotient nilpotence of a prime, a divided-power ideal is locally
nilpotent exactly when that prime is nilpotent in the ambient ring. -/
@[stacks 07GR]
#check (DividedPowers.isLocallyNilpotent_iff_isNilpotent_natCast gamma :
  IsNilpotent (p : A ⧸ I) →
    (I.IsLocallyNilpotent ↔ IsNilpotent (p : A)))

end

#check @Ideal.IsLocallyNilpotent.isNilpotent_natCast_of_quotient
#check @DividedPowers.isLocallyNilpotent_of_isNilpotent_natCast
