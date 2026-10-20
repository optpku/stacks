module

public import ReasLib.RingTheory.DividedPowers.Quotient
import StacksCheckRecall

@[expose] public section

universe u v

section Kernel

variable {A : Type u} [CommRing A] {I : Ideal A}
variable (gamma : DividedPowers I) {B : Type v} [CommRing B] {J : Ideal B}
variable (delta : DividedPowers J) (f : A →+* B)
variable (hf : gamma.IsDPMorphism delta f)

/- Lemma 23.4.3 (1) (07H2): the kernel of a divided-power morphism, intersected with the source
divided-power ideal, is a sub-divided-power ideal. -/
@[stacks 07H2 "(1)"]
#check (DividedPowers.isSubDPIdeal_ker gamma delta hf :
  gamma.IsSubDPIdeal (RingHom.ker f ⊓ I))

end Kernel

section Quotient

variable {A : Type u} [CommRing A] {I : Ideal A}
variable (gamma : DividedPowers I) (a : Ideal A)

/- Lemma 23.4.3 (2) (07H2): preservation of the intersection with an ideal is equivalent to
extension along the quotient map. -/
@[stacks 07H2 "(2)"]
#check (DividedPowers.isSubDPIdeal_inf_iff_extendsAlong_quotientMk gamma a :
  gamma.IsSubDPIdeal (a ⊓ I) ↔ gamma.extendsAlong (Ideal.Quotient.mk a))

/- Lemma 23.4.3 (3) (07H2): the same condition is equivalent to the existence of a generating
set stable under all positive divided powers. -/
@[stacks 07H2 "(3)"]
#check (DividedPowers.isSubDPIdeal_inf_iff_exists_generatingSet gamma a :
  gamma.IsSubDPIdeal (a ⊓ I) ↔
    ∃ S : Set A,
      Ideal.span S = a ⊓ I ∧
        ∀ n : ℕ, n ≠ 0 → ∀ s : A, s ∈ S → gamma.dpow n s ∈ Ideal.span S)

end Quotient

#check @DividedPowers.isSubDPIdeal_inf_iff_exists_quotientDividedPowers
#check @DividedPowers.isSubDPIdeal_inf_iff_span_eq
