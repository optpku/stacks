module

public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal smoothness across square-zero quotient extensions

This leaf packages the common quotient-by-the-same-ideal specialization of
the general flat quotient-descent theorem.  The ideal and the flatness proof
remain explicit, so a one-off flatness result does not need to be installed as
a local instance by downstream users.

@stack 031L
-/

@[expose] public section

universe u v

namespace Algebra.FormallySmooth

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `031L`: formal smoothness ascends across a square-zero ideal when the
source algebra is flat and the induced quotient algebra is formally smooth. -/
@[stacks 031L "square-zero quotient formal smoothness"]
theorem of_squareZeroIdeal_of_flat
    (I : Ideal R) (hflat : Module.Flat R S) (hSq : I ^ 2 = ⊥)
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    Algebra.FormallySmooth R S := sorry

end Algebra.FormallySmooth
