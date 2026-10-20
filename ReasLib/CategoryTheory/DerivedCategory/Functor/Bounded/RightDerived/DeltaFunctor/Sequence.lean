/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.DeltaFunctor.Connecting
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Windows of Bounded-Below Right Derived Functors

The standard six-term window is stated directly with the degree functors
`RⁿF` and their connecting map. Its data is constructed explicitly rather
than transported through an equality of functors.
-/

open CategoryTheory
open CategoryTheory.ComposableArrows
open scoped CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.cohomological

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
  [RF.CommShift ℤ] [RF.IsTriangulated]

/-- The six-object exact window around the degree-`n` connecting map of a
bounded-below right-derived functor. -/
@[stacks 05TE "exact window of bounded-below right-derived functors"]
def exactWindow {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows B 5 :=
  mk₅ ((RightDerived.degree RF (n : ℤ)).map S.f)
    ((RightDerived.degree RF (n : ℤ)).map S.g) (connecting RF hS n)
    ((RightDerived.degree RF (n + 1 : ℕ)).map S.f)
    ((RightDerived.degree RF (n + 1 : ℕ)).map S.g)

/-- The canonical right-derived window is exact. -/
@[stacks 05TE "exactness of the bounded-below right-derived window"]
theorem exactWindow_exact {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (exactWindow RF hS n).Exact := sorry

/-- Applying a bounded-below right-derived degree functor to a short exact
sequence gives an exact short complex. -/
@[stacks 05TE "exactness within one bounded-below right-derived degree"]
theorem map_exact {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (S.map (RightDerived.degree RF (n : ℤ))).Exact := sorry

/-- Exactness at the term before the right-derived connecting map. -/
@[stacks 05TE "exactness before a bounded-below right-derived connecting map"]
theorem exact_map_g_connecting {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk ((RightDerived.degree RF (n : ℤ)).map S.g)
      (connecting RF hS n) (map_g_comp_connecting RF hS n)).Exact := sorry

/-- Exactness at the term after the right-derived connecting map. -/
@[stacks 05TE "exactness after a bounded-below right-derived connecting map"]
theorem exact_connecting_map_f {S : ShortComplex A}
    (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (connecting RF hS n)
      ((RightDerived.degree RF (n + 1 : ℕ)).map S.f)
      (connecting_comp_map_f RF hS n)).Exact := sorry

/-- The low-degree exact window of a bounded-below right-derived functor. -/
abbrev lowDegreeWindow {S : ShortComplex A} (hS : S.ShortExact) :
    ComposableArrows B 5 :=
  exactWindow RF hS 0

/-- The low-degree right-derived window is exact. -/
@[stacks 05TE "exactness of the low-degree right-derived window"]
theorem lowDegreeWindow_exact {S : ShortComplex A} (hS : S.ShortExact) :
    (lowDegreeWindow RF hS).Exact := sorry

end CategoryTheory.Functor.RightDerived.cohomological
