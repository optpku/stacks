/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalProperties.Exactness
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of the Principal-Open Cech Complex

Mathlib's localized-span criterion detects exactness after restriction to a
principal-open cover.  This leaf specializes that criterion to the explicit
Cech maps from `LocalizedModule.Away.Cech`.
-/

@[expose] public section

universe u v w

namespace LocalizedModule.Away.Cech

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/-- Tag `00EK`: if one denominator already acts by units on `M`, the
principal-open Cech family map is injective. -/
@[stacks 00EK "unit principal-open Cech family map injective"]
theorem familyMap_injective_of_isUnit
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i : ι)
    (hunit : ∀ s : Submonoid.powers (f i),
      IsUnit (algebraMap R (Module.End R M) s)) :
    Function.Injective (familyMap M f) := sorry

/-- Tag `00EK`: if one denominator already acts by units on `M`, the
principal-open Cech family map is exact at the middle term. -/
@[stacks 00EK "unit principal-open Cech exactness"]
theorem familyMap_exact_of_isUnit
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i : ι)
    (hunit : ∀ s : Submonoid.powers (f i),
      IsUnit (algebraMap R (Module.End R M) s)) :
    Function.Exact (familyMap M f) (compatibilityMap M f) := sorry

/-- Tag `00EK`: the principal-open Cech family map is injective when the
denominators generate the unit ideal. -/
@[stacks 00EK "principal-open Cech family map injective"]
theorem familyMap_injective
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (familyMap M f) := sorry

/-- Tag `00EK`: the kernel of the principal-open Cech differential is the
image of the family map when the denominators generate the unit ideal. -/
@[stacks 00EK "principal-open Cech exactness"]
theorem familyMap_exact
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (familyMap M f) (compatibilityMap M f) := sorry

end LocalizedModule.Away.Cech
