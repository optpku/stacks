/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ScalarQuotient.Determinant
import StacksCheckRecall

@[expose] public section

open scoped nonZeroDivisors

universe u v

section ModuleCase

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
variable (hdim : Module.supportDim A M = 1)

/- Lemma 42.68.28 (1): if `a` and `b` are regular on a finite dimension-one module `M`
over a Noetherian local ring `A`, then `M ⧸ (a * b) • ⊤` has finite length. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotient_length_lt_top
    M a b ha hb hdim : Module.length A (QuotSMulTop (a * b) M) < ⊤)

/- Lemma 42.68.28 (2): under the same hypotheses, multiplication by `a` and `b` on
`M ⧸ (a * b) • ⊤` gives an acyclic two-periodic complex. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotient_acyclic
    M a b ha hb hdim :
      (CategoryTheory.TwoPeriodicEndomorphism.ofScalarQuotient M a b).toCochainComplex.Acyclic)

end ModuleCase

section RingCase

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1)

/- Lemma 42.68.28 (3): if `a` and `b` are nonzerodivisors in a dimension-one
Noetherian local ring `A`, then `A ⧸ (a * b) • ⊤` has finite length. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotient_self_length_lt_top
    a b ha hb hdim : Module.length A (QuotSMulTop (a * b) A) < ⊤)

/- Lemma 42.68.28 (4): multiplication by two nonzerodivisors `a` and `b` on
`A ⧸ (a * b) • ⊤` gives an acyclic two-periodic complex. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotient_self_acyclic
    a b ha hb hdim :
      (CategoryTheory.TwoPeriodicEndomorphism.ofScalarQuotient A a b).toCochainComplex.Acyclic)

end RingCase

section ModuleDeterminant

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
variable (hdim : Module.supportDim A M = 1)

/- Lemma 42.68.28 (5): the periodic determinant of the scalar quotient complex of `M`
is a unit of the residue field of `A`. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientDeterminant
    M a b ha hb hdim : (IsLocalRing.ResidueField A)ˣ)

end ModuleDeterminant

section RingDeterminant

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable (a b : A) (ha : a ∈ A⁰) (hb : b ∈ A⁰) (hdim : ringKrullDim A = 1)

/- Lemma 42.68.28 (6): the periodic determinant of the scalar quotient complex of `A`
is a unit of the residue field of `A`. -/
@[stacks 02PY] #check
  (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
    a b ha hb hdim : (IsLocalRing.ResidueField A)ˣ)

end RingDeterminant
