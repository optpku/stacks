module

public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension

@[expose] public section

/-!
# Uniform Homological Dimension

Uniform projective- and injective-dimension bounds are equivalent in an abelian category: both
say that the same higher extension groups vanish, with the source or target allowed to vary.
-/

universe v u

namespace CategoryTheory.HomologicalDimension

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A uniform projective-dimension bound supplies the same injective-dimension bound on every
target object. -/
theorem injectiveLE_of_projectiveLE {n : ℕ}
    (h : ∀ X : C, HasProjectiveDimensionLE X n) (Y : C) :
    HasInjectiveDimensionLE Y n := sorry

/-- A uniform injective-dimension bound supplies the same projective-dimension bound on every
source object. -/
theorem projectiveLE_of_injectiveLE {n : ℕ}
    (h : ∀ Y : C, HasInjectiveDimensionLE Y n) (X : C) :
    HasProjectiveDimensionLE X n := sorry

/-- Uniform projective- and injective-dimension bounds agree in every abelian category. -/
theorem projectiveLE_iff_injectiveLE (n : ℕ) :
    (∀ X : C, HasProjectiveDimensionLE X n) ↔
      ∀ Y : C, HasInjectiveDimensionLE Y n := sorry

end CategoryTheory.HomologicalDimension
