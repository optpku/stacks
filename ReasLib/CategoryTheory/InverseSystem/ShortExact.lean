module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.ShortComplex.FunctorCategory
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Exactness of Inverse Systems

Exactness and short exactness of inverse-system rows are detected by evaluation at every stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Evaluate a sequential inverse-system short complex at the natural-number stage `i`. -/
abbrev app (S : CategoryTheory.ShortComplex (SequentialInverseSystem C)) (i : ℕ) :
    CategoryTheory.ShortComplex C :=
  CategoryTheory.ShortComplex.FunctorCategory.app S (op i)

/-- Exactness of a sequential inverse-system short complex is detected at every stage. -/
@[stacks 02MZ]
theorem exact_iff_exact_app
    (S : CategoryTheory.ShortComplex (SequentialInverseSystem C)) :
    S.Exact ↔ ∀ i : ℕ, (app S i).Exact := sorry

namespace ShortExact

/-- Evaluation preserves short exactness for sequential inverse systems. -/
theorem app {S : CategoryTheory.ShortComplex (SequentialInverseSystem C)} {i : ℕ}
    (hS : S.ShortExact) :
    (SequentialInverseSystem.ShortComplex.app S i).ShortExact := sorry

end ShortExact

end CategoryTheory.SequentialInverseSystem.ShortComplex
