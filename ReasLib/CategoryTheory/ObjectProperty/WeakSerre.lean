/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak Serre Classes

A weak Serre subcategory of an abelian category is a nonempty full subcategory satisfying the
four-out-of-five exactness criterion: in every exact sequence `A₀ → A₁ → A₂ → A₃ → A₄`,
membership of A₀, A₁, A₃, A₄ forces membership of A₂.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A weak Serre subcategory is a nonempty full subcategory such that in every exact sequence
`A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄`, membership of `A₀`, `A₁`, `A₃`, and `A₄` forces membership of
`A₂`. -/
@[stacks 02MO]
class IsWeakSerreClass (P : ObjectProperty A) : Prop extends P.Nonempty where
  prop_X₂_of_exact₄ {S : ComposableArrows A 4} (hS : S.Exact)
      (h₀ : P (S.obj 0)) (h₁ : P (S.obj 1)) (h₃ : P (S.obj 3)) (h₄ : P (S.obj 4)) :
      P (S.obj 2)

variable (P : ObjectProperty A)

/-- The canonical closure-based Serre-class structure is equivalent to closure of the middle
object in every exact short complex. -/
@[stacks 02MP]
theorem isSerreClass_iff_exact :
    P.IsSerreClass ↔
      P.Nonempty ∧
        ∀ (S : ShortComplex A), S.Exact → P S.X₁ → P S.X₃ → P S.X₂ := sorry

/-- The smallest weak Serre object property containing `P`. -/
def weakSerreClosure : ObjectProperty A :=
  sInf {Q : ObjectProperty A | IsWeakSerreClass Q ∧ P ≤ Q}

/-- Every generator belongs to its weak Serre closure. -/
theorem le_weakSerreClosure : P ≤ weakSerreClosure P := sorry

namespace weakSerreClosure

/-- The weak Serre closure is itself a weak Serre class. -/
instance isWeakSerre : IsWeakSerreClass (weakSerreClosure P) := sorry

end weakSerreClosure

/-- The weak Serre closure is contained in every weak Serre class containing the generators. -/
theorem weakSerreClosure_le (Q : ObjectProperty A) [IsWeakSerreClass Q] (hPQ : P ≤ Q) :
    weakSerreClosure P ≤ Q := sorry

namespace IsClosedUnderExtensions

/-- Closure under extensions together with a zero object implies closure under isomorphisms. -/
theorem closedUnderIsomorphisms [P.ContainsZero] [P.IsClosedUnderExtensions] :
    P.IsClosedUnderIsomorphisms := sorry

end IsClosedUnderExtensions

namespace IsWeakSerreClass

/-- A weak Serre class contains a zero object. -/
instance containsZero [IsWeakSerreClass P] : P.ContainsZero := sorry

/-- A weak Serre class is closed under kernels. -/
instance closedUnderKernels [IsWeakSerreClass P] :
    P.IsClosedUnderKernels := sorry

/-- A weak Serre class is closed under cokernels. -/
instance closedUnderCokernels [IsWeakSerreClass P] :
    P.IsClosedUnderCokernels := sorry

/-- A weak Serre class is closed under extensions. -/
instance closedUnderExtensions [IsWeakSerreClass P] :
    P.IsClosedUnderExtensions := sorry

/-- A weak Serre class is closed under isomorphisms. -/
instance closedUnderIsomorphisms [IsWeakSerreClass P] :
    P.IsClosedUnderIsomorphisms := sorry

/-- A weak Serre class is stable under retracts. -/
@[stacks 06UQ "retract stability of weak Serre subcategories"]
instance stableUnderRetracts [IsWeakSerreClass P] :
    P.IsStableUnderRetracts := sorry

/-- A weak Serre class is closed under binary products. -/
instance closedUnderBinaryProducts [IsWeakSerreClass P] :
    P.IsClosedUnderBinaryProducts := sorry

/-- A weak Serre class is closed under finite products. -/
instance closedUnderFiniteProducts [IsWeakSerreClass P] :
    P.IsClosedUnderFiniteProducts := sorry

/-- In a short exact sequence, if the left and right terms belong to a weak Serre class, then
so does the middle term. -/
@[stacks 01BY "(4), middle term"]
theorem prop_X₂_of_shortExact [IsWeakSerreClass P] {S : ShortComplex A}
    (hS : S.ShortExact) (h₁ : P S.X₁) (h₃ : P S.X₃) : P S.X₂ := sorry

/-- In a short exact sequence, if the middle and right terms belong to a weak Serre class,
then so does the left term. -/
@[stacks 01BY "(4), left term"]
theorem prop_X₁_of_shortExact [IsWeakSerreClass P] {S : ShortComplex A}
    (hS : S.ShortExact) (h₂ : P S.X₂) (h₃ : P S.X₃) : P S.X₁ := sorry

/-- In a short exact sequence, if the left and middle terms belong to a weak Serre class,
then so does the right term. -/
@[stacks 01BY "(4), right term"]
theorem prop_X₃_of_shortExact [IsWeakSerreClass P] {S : ShortComplex A}
    (hS : S.ShortExact) (h₁ : P S.X₁) (h₂ : P S.X₂) : P S.X₃ := sorry

/-- The closure-package characterization: a nonempty subcategory closed under kernels,
cokernels, and extensions is a weak Serre subcategory. -/
@[stacks 02MO]
theorem ofClosure [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    IsWeakSerreClass P := sorry

/-- Every Serre class is a weak Serre class. -/
instance ofIsSerreClass [P.IsSerreClass] : IsWeakSerreClass P := sorry

namespace Inclusion

/-- The inclusion of a weak Serre full subcategory into its ambient abelian category is exact. -/
@[stacks 0754 "exact inclusion of a weak Serre subcategory"]
theorem isExact [IsWeakSerreClass P] :
    exactFunctor P.FullSubcategory A P.ι := sorry

/-- The inclusion of a weak Serre full subcategory preserves finite limits. -/
instance preservesFiniteLimits [IsWeakSerreClass P] :
    PreservesFiniteLimits P.ι := sorry

/-- The inclusion of a weak Serre full subcategory preserves finite colimits. -/
instance preservesFiniteColimits [IsWeakSerreClass P] :
    PreservesFiniteColimits P.ι := sorry

end Inclusion

end IsWeakSerreClass

end CategoryTheory.ObjectProperty
