/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization properties of approximation base-change maps

This leaf keeps localization properties of `Hom.baseChangeMap` independent
from the map construction itself.  The lightweight surjective, injective, and
bijective API lives in `BaseChange.Bijective`; localization data can therefore
be reused by local and essential-finiteness arguments without importing a
larger source-facing approximation owner.
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Every transition base-change map presents its target as a localization of
a quotient of the corresponding tensor source. -/
@[stacks 00R1 "directed approximation base-change property"]
def baseChange_isLocalizationOfQuotient (A : Hom f) : Prop :=
  ∀ {i j : A.index} (h : i ≤ j),
    RingHom.IsLocalizationOfQuotient (A.baseChangeMap h)

/-- Read one localization-of-quotient transition from the bundled property. -/
@[stacks 00R1 "directed approximation base-change property"]
theorem baseChange_isLocalizationOfQuotient_at (A : Hom f)
    (hA : A.baseChange_isLocalizationOfQuotient)
    {i j : A.index} (h : i ≤ j) :
    RingHom.IsLocalizationOfQuotient (A.baseChangeMap h) := sorry

/-!
The prime-localization predicate is kept separate from
`baseChange_isLocalizationOfQuotient`: a localization at a prime is a
strictly more structured witness, and many arguments need the named prime
without any quotient presentation.
-/

/-- Every transition base-change map presents its target as a localization at
a prime ideal of the corresponding tensor-product source. -/
@[stacks 00R1 "directed approximation base-change property"]
def baseChange_isLocalizationAtPrime (A : Hom f) : Prop :=
  ∀ {i j : A.index} (h : i ≤ j),
    ∃ p : Ideal (A.baseChange h),
      ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap (A.baseChangeMap h)

/-! The one-transition reader keeps callers independent of the bundled
predicate's implementation. -/

/-- Read one prime-localization transition from the bundled property. -/
@[stacks 00R1 "directed approximation base-change property"]
theorem baseChange_isLocalizationAtPrime_at (A : Hom f)
    (hA : A.baseChange_isLocalizationAtPrime)
    {i j : A.index} (h : i ≤ j) :
    ∃ p : Ideal (A.baseChange h),
      ∃ _ : p.IsPrime, p.primeCompl.IsLocalizationMap (A.baseChangeMap h) := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
