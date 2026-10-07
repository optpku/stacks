module

public import ReasLib.Algebra.Module.IdealPower.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCech

import Mathlib.Tactic.CrossRefAttribute

/-!
# The module Beauville-Laszlo criterion

Under compatibility of all positive-power quotients, exactness of the module Cech sequence is
controlled by the base-change map on power-torsion submodules.

@stack 0BNW
-/

@[expose] public section

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Lemma 15.91.10 (1): positive-power quotient compatibility makes the module Cech sequence
exact on the right. -/
@[stacks 0BNW "Lemma 15.91.10 (1)"]
theorem beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Surjective ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := sorry

/-- Lemma 15.91.10 (2): left exactness is equivalent to injectivity on power torsion. -/
@[stacks 0BNW "Lemma 15.91.10 (2)"]
theorem beauvilleLaszloModuleCechLeftMap_injective_iff_fPowerTorsionToTensor_injective
    (f : R) :
    Function.Injective ((beauvilleLaszloModuleCechSequence R' M f).f.hom) ↔
      Function.Injective
        (Ideal.primaryComponent.baseChangeUnit
          (algebraMap R R') (principalIdeal f) M) := sorry

/-- Lemma 15.91.10 (3): under positive-power quotient compatibility, middle exactness is
equivalent to surjectivity on power torsion. -/
@[stacks 0BNW "Lemma 15.91.10 (3)"]
theorem beauvilleLaszloModuleCech_exact_iff_fPowerTorsionToTensor_surjective
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) ↔
    Function.Surjective
      (Ideal.primaryComponent.baseChangeUnit
        (algebraMap R R') (principalIdeal f) M) := sorry

/-- Lemma 15.91.10 (4): module glueability is equivalent to bijectivity on power torsion. -/
@[stacks 0BNW "Lemma 15.91.10 (4)"]
theorem isBeauvilleLaszloGlueableAlong_iff_bijective_fPowerTorsionToTensor
    (f : R) (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Bijective
        (Ideal.primaryComponent.baseChangeUnit
          (algebraMap R R') (principalIdeal f) M) := sorry

/-- Lemma 15.91.10 (5): for a glueing pair, module glueability is equivalent to injectivity on
power torsion. -/
@[stacks 0BNW, stacks 0BP8 "Lemma 15.91.10 (5)"]
theorem isBeauvilleLaszloGlueableAlong_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R' M f).ShortExact ↔
      Function.Injective
        (Ideal.primaryComponent.baseChangeUnit
          (algebraMap R R') (principalIdeal f) M) := sorry

end

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Lemma 15.91.10 (6): specialization of the glueing-pair criterion to principal-adic
completion. -/
@[stacks 0BNW "Lemma 15.91.10 (6)"]
theorem isBeauvilleLaszloGlueableAlong_principalAdicCompletion_iff_injective_fPowerTorsionToTensor_of_glueingPair
    (f : R)
    (hpair : IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f) :
    (beauvilleLaszloModuleCechSequence (principalAdicCompletion f) M f).ShortExact ↔
      Function.Injective
        (Ideal.primaryComponent.baseChangeUnit
          (algebraMap R (principalAdicCompletion f)) (principalIdeal f) M) := sorry

end
