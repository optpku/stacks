/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Glue
import StacksCheckRecall

@[expose] public section

universe u

section

variable {A : Type u} [CommRing A] {I J : Ideal A}
variable (gamma : DividedPowers I) (delta : DividedPowers J)

/- Lemma 23.2.5 (1) (07GQ): divided power structures on two ideals agree on their product. -/
@[stacks 07GQ "(1)"]
#check (DividedPowers.coincide_on_mul gamma delta :
  ∀ {n : ℕ} {x : A}, x ∈ I * J → gamma.dpow n x = delta.dpow n x)

/- Lemma 23.2.5 (2) (07GQ): structures agreeing on the intersection glue uniquely to the
supremum ideal; the canonical structure is explicit convolution data. -/
@[stacks 07GQ "(2), canonical gluing"]
#check (DividedPowers.existsUnique_sup_of_agreeOnInf gamma delta :
  DividedPowers.agreeOnInf gamma delta →
    ∃! epsilon : DividedPowers (I ⊔ J),
      DividedPowers.compatibleOnSup gamma delta epsilon)

end

#check @DividedPowers.agreeOnInf
#check @DividedPowers.compatibleOnSup
#check @DividedPowers.glue_dpow_add
#check @DividedPowers.glue_dpow_of_mem_left
#check @DividedPowers.glue_dpow_of_mem_right
#check @DividedPowers.glue_compatibleOnSup
#check @DividedPowers.eq_glue
#check @DividedPowers.existsUnique_sup_of_agreeOnInf
#check @DividedPowers.existsUnique_sup_iff_agreeOnInf
