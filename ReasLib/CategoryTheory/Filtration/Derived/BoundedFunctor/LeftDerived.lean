/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedFunctor.Minus
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Bounded-above left-derived comparisons

The former graded-piece and forgetful comparison wrappers in this leaf were just
specializations of `Functor.leftDerivedUnique` with no Stacks source statement and no
library consumer.  Keep the import path for the aggregator, while clients use the
mathlib uniqueness theorem directly.
-/
