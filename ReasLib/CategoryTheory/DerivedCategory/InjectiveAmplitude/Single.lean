module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import ReasLib.CategoryTheory.DerivedCategory.InjectiveAmplitude

/-!
# Injective amplitude of single objects

This file connects the categorical injective dimension of an object in the heart with the
injective amplitude of its image under the canonical single-object functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
variable [HasDerivedCategory.{w} C]

/-- An injective-dimension bound on a heart object gives the corresponding amplitude bound on
the object placed in degree `i`. -/
theorem hasInjectiveAmplitudeIn_single_of_injectiveDimension_le
    (M : C) (i : ℤ) (m : ℕ) (hM : injectiveDimension M ≤ m) :
    HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor C i).obj M)
      i (i + (m : ℤ)) := sorry

/-- The amplitude supplied by an injective-dimension bound may be enlarged to any containing
interval. -/
theorem hasInjectiveAmplitudeIn_single_of_injectiveDimension_le_of_bounds
    (M : C) (i a b : ℤ) (m : ℕ) (hM : injectiveDimension M ≤ m)
    (ha : a ≤ i) (hb : i + (m : ℤ) ≤ b) :
    HasInjectiveAmplitudeIn ((DerivedCategory.singleFunctor C i).obj M) a b := sorry

/-- A heart object of finite injective dimension gives a derived object of finite injective
dimension in every degree. -/
theorem hasFiniteInjectiveDimension_single_of_injectiveDimension_ne_top
    (M : C) (i : ℤ) (hM : injectiveDimension M ≠ ⊤) :
    HasFiniteInjectiveDimension ((DerivedCategory.singleFunctor C i).obj M) := sorry

end CategoryTheory.DerivedCategory
