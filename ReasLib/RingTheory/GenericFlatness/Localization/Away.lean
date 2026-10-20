/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.GenericFlatness.Localization

/-!
# Principal-localization transport for generic flatness

This leaf records the functoriality of `LocalizationCondition` under principal
localization.  Its statements use `LocalizationCondition.away` so that the
relative scalar action is fixed explicitly and never enters global instance
search.
-/

@[expose] public section

universe u v w

namespace GenericFlatness.LocalizationCondition

/-- Direct finite-presentation and freeness hypotheses imply the generic-flatness localization
condition at every principal parameter. -/
theorem ofUnlocalized
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
    (f : R)
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
    [Module.Free R S] [Module.Free R M] :
    LocalizationCondition R S M f := sorry

/-- At a unit parameter, the generic-flatness localization condition is equivalent to the four
unlocalized finite-presentation and freeness properties. -/
theorem unlocalized_iff_of_isUnit
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M] [Module R M] [IsScalarTower R S M]
    {f : R} (hf : IsUnit f) :
    LocalizationCondition R S M f ↔
      Algebra.FinitePresentation R S ∧ Module.FinitePresentation S M ∧
        Module.Free R S ∧ Module.Free R M := sorry

/-- Associated principal parameters determine equivalent generic-flatness localization
conditions. -/
theorem associated_iff
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    {f g : R} (hfg : Associated f g) :
    LocalizationCondition R S M f ↔ LocalizationCondition R S M g := sorry

/-- The condition at the product `f * g` is equivalent to the condition obtained by first
localizing away from `f` and then at the image of `g`. -/
theorem product_iff_away
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    (f g : R) :
    LocalizationCondition R S M (f * g) ↔
      LocalizationCondition.away (R := R) (S := S) (M := M) f
        (algebraMap R (Localization.Away f) g) := sorry

/-- A generic-flatness witness remains a witness after localizing the whole algebra-module pair
away from an arbitrary base parameter. -/
theorem mapAway
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    (f g : R) (hg : LocalizationCondition R S M g) :
    LocalizationCondition.away (R := R) (S := S) (M := M) f
      (algebraMap R (Localization.Away f) g) := sorry

/-- A witness at an arbitrary point of `R_f` clears to an explicit principal witness over `R`. -/
theorem ofLocalizedWitness
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    (f : R) (u : Localization.Away f)
    (hu : LocalizationCondition.away (R := R) (S := S) (M := M) f u) :
    LocalizationCondition R S M (f * (IsLocalization.Away.sec f u).1) := sorry

/-- A generic-flatness witness remains valid after multiplying its denominator by any element of
the base ring. -/
theorem mul
    {R : Type u} [CommSemiring R]
    {S : Type v} [CommSemiring S] [Algebra R S]
    {M : Type w} [AddCommMonoid M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition R S M (f * g) := sorry

end GenericFlatness.LocalizationCondition
