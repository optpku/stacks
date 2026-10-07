module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import ReasLib.CategoryTheory.DerivedCategory.ProjectiveAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective amplitude of single objects

This file connects projective objects and projective-dimension bounds in the heart with the
projective amplitude of their images under the canonical single-object functor.

@stack 0A5N
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- A projective object placed in degree `i` has projective amplitude in `[i, i]`. -/
@[stacks 0A5N "projective amplitude of a single projective object"]
theorem hasProjectiveAmplitudeIn_single_of_projective
    (M : C) (i : ℤ) (hM : Projective M) :
    HasProjectiveAmplitudeIn ((DerivedCategory.singleFunctor C i).obj M) i i := sorry

section EnoughProjectives

variable [EnoughProjectives C]

/-- A projective-dimension bound on a heart object gives the corresponding amplitude bound on
the object placed in degree `i`. -/
@[stacks 0A5N "projective dimension bound for a single object"]
theorem hasProjectiveAmplitudeIn_single_of_projectiveDimension_le
    (M : C) (i : ℤ) (m : ℕ) (hM : projectiveDimension M ≤ m) :
    HasProjectiveAmplitudeIn ((DerivedCategory.singleFunctor C i).obj M)
      (i - (m : ℤ)) i := sorry

/-- The amplitude supplied by a projective-dimension bound may be enlarged to any containing
interval. -/
@[stacks 0A5N "enlarged projective amplitude for a single object"]
theorem hasProjectiveAmplitudeIn_single_of_projectiveDimension_le_of_bounds
    (M : C) (i a b : ℤ) (m : ℕ) (hM : projectiveDimension M ≤ m)
    (ha : a ≤ i - (m : ℤ)) (hb : i ≤ b) :
    HasProjectiveAmplitudeIn ((DerivedCategory.singleFunctor C i).obj M) a b := sorry

/-- A heart object of finite projective dimension gives a derived object of finite projective
dimension in every degree. -/
@[stacks 0A5N "finite projective dimension of a single object"]
theorem hasFiniteProjectiveDimension_single_of_projectiveDimension_ne_top
    (M : C) (i : ℤ) (hM : projectiveDimension M ≠ ⊤) :
    HasFiniteProjectiveDimension ((DerivedCategory.singleFunctor C i).obj M) := sorry

end EnoughProjectives

end CategoryTheory.DerivedCategory
