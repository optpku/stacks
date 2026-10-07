module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints

@[expose] public section

/-!
# Lemma 15.111.8: transitivity over the fixed subring

@stack 0BRI
-/

open scoped Pointwise

universe u v

/-
Lemma 15.111.8 (current Stacks numbering: Lemma 15.112.8, tag `0BRI`): if two prime ideals of a
commutative ring `R` lie over the same prime ideal of the fixed-point subring `R^G`, then one is
obtained from the other by the action of an element of the finite group `G`.

This is the fixed-subring specialization of the canonical invariant-extension transitivity
theorem.  Equality symmetry only changes the displayed orientation of the source conclusion.
-/

section

variable {R : Type u} {G : Type v}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]

@[stacks 0BRI "prime ideals over the fixed subring form one orbit"]
#check fun (p : Ideal (FixedPoints.subring R G)) (q q' : Ideal R)
    [q.IsPrime] [q'.IsPrime] [q.LiesOver p] [q'.LiesOver p] ↦
  ((Algebra.IsInvariant.exists_smul_of_under_eq
      (FixedPoints.subring R G) R G q q'
      ((q.over_def p).symm.trans (q'.over_def p))).imp (fun _ hσ ↦ hσ.symm) :
    ∃ σ : G, σ • q = q')

end
