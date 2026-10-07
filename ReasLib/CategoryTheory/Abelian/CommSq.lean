module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Limits
open ComposableArrows ZeroObject

universe v u

namespace CategoryTheory

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-- 08N2 (Lemma 12.5.11 (1)): a commutative square in an abelian category is a pullback exactly
when its canonical sequence `0 ⟶ W ⟶ X ⊞ Y ⟶ Z` is exact. -/
@[stacks 08N2]
theorem isPullback_iff_exact_biproduct_sequence (sq : CommSq g f k h) :
    IsPullback g f k h ↔
      (mk₃ (0 : 0 ⟶ W) sq.shortComplex'.f sq.shortComplex'.g).Exact := sorry

/-- 08N2 (Lemma 12.5.11 (2)): a commutative square in an abelian category is a pushout exactly
when its canonical sequence `W ⟶ X ⊞ Y ⟶ Z ⟶ 0` is exact. -/
@[stacks 08N2]
theorem isPushout_iff_exact_biproduct_sequence (sq : CommSq g f k h) :
    IsPushout g f k h ↔
      (mk₃ sq.shortComplex.f sq.shortComplex.g (0 : Z ⟶ 0)).Exact := sorry

/-- In an abelian category, a pullback square with an epimorphic right leg is a pushout square. -/
@[stacks 08N4]
theorem isPushout_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    IsPushout g f k h := sorry

/-- In a pullback square in an abelian category, an epimorphic right leg forces the left leg to
be epimorphic. -/
@[stacks 08N4]
theorem epi_left_of_isPullback_of_epi_right [Epi k] (sq : IsPullback g f k h) :
    Epi f := sorry

/-- In an abelian category, a pushout square with a monomorphic top leg is a pullback square. -/
@[stacks 08N4]
theorem isPullback_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    IsPullback g f k h := sorry

/-- In a pushout square in an abelian category, a monomorphic top leg forces the bottom leg to
be monomorphic. -/
@[stacks 08N4]
theorem mono_bottom_of_isPushout_of_mono_top [Mono g] (sq : IsPushout g f k h) :
    Mono h := sorry

end

end CategoryTheory
