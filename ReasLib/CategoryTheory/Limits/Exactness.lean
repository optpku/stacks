module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generating-shape criteria for exact functors

Left and right exactness can be checked on the standard generating finite (co)limit shapes.
Each criterion is a direct equivalence so downstream code can rewrite without TFAE indices.
-/

@[expose] public section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace leftExactFunctor

/-- Lemma 4.23.2 (1) (Stacks 0035): left exactness is equivalent to preservation of finite
products and equalizers. -/
@[stacks 0035 "finite products and equalizers characterize left exactness"]
theorem iff_preservesFiniteProducts_and_equalizers
    [HasFiniteLimits C] (F : C ⥤ D) :
    leftExactFunctor C D F ↔
      PreservesFiniteProducts F ∧ PreservesLimitsOfShape WalkingParallelPair F := sorry

/-- Lemma 4.23.2 (2) (Stacks 0035): left exactness is equivalent to preservation of terminal
objects and pullbacks. -/
@[stacks 0035 "terminal objects and pullbacks characterize left exactness"]
theorem iff_preservesTerminal_and_pullbacks
    [HasFiniteLimits C] (F : C ⥤ D) :
    leftExactFunctor C D F ↔
      PreservesLimit (Functor.empty.{0} C) F ∧
        PreservesLimitsOfShape WalkingCospan F := sorry

end leftExactFunctor

namespace rightExactFunctor

/-- Lemma 4.23.3 (1) (Stacks 0GMN): right exactness is equivalent to preservation of finite
coproducts and coequalizers. -/
@[stacks 0GMN "finite coproducts and coequalizers characterize right exactness"]
theorem iff_preservesFiniteCoproducts_and_coequalizers
    [HasFiniteColimits C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesFiniteCoproducts F ∧
        PreservesColimitsOfShape WalkingParallelPair F := sorry

/-- Lemma 4.23.3 (2) (Stacks 0GMN): right exactness is equivalent to preservation of initial
objects and pushouts. -/
@[stacks 0GMN "initial objects and pushouts characterize right exactness"]
theorem iff_preservesInitial_and_pushouts
    [HasFiniteColimits C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesColimit (Functor.empty.{0} C) F ∧
        PreservesColimitsOfShape WalkingSpan F := sorry

end rightExactFunctor

end CategoryTheory
