/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Pro.Sequential.Homology.Value
public import ReasLib.CategoryTheory.Pro.Sequential.Zero
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential derived towers with pro-zero negative homology

The presentation-independent condition is stated using `Pro.HasValue`.  A companion theorem
recovers the eventual vanishing of transition maps used in concrete sequential presentations.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped ZeroObject

universe w u v

namespace CategoryTheory.DerivedCategory.Pro.Sequential.Homology

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

namespace Negative

/-- A sequential derived tower has pro-zero homology in every strictly negative degree. -/
@[stacks 0H1E "pro-zero negative homology of a sequential derived tower"]
def IsProZero (K : SequentialInverseSystem (DerivedCategory A)) : Prop :=
  ∀ p : ℕ, 0 < p →
    _root_.CategoryTheory.Pro.HasValue
      (K ⋙ DerivedCategory.homologyFunctor A (-(p : ℤ))) (0 : A)

/-- Pro-zero negative homology is equivalent to eventual vanishing of every negative-degree
homology transition system. -/
theorem isProZero_iff_eventuallyZeroTransitions
    (K : SequentialInverseSystem (DerivedCategory A)) :
    IsProZero K ↔
      ∀ p : ℕ, 0 < p →
        PreorderInverseSystem.Transition.EventuallyZero
          (K ⋙ DerivedCategory.homologyFunctor A (-(p : ℤ))) := sorry

end Negative
end CategoryTheory.DerivedCategory.Pro.Sequential.Homology
