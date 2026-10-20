/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
import StacksCheckRecall

/-!
# Derived tensor product under change of rings

This chapter file recalls the canonical change-of-rings derived tensor API from `ReasLib`.

@stack 06Y6
-/

@[expose] public section

/- Lemma 15.60.1 (1), tag `06Y6`: derived tensoring over the source ring is the composite of
derived scalar extension and derived tensoring over the target ring. -/
@[stacks 06Y6 "(1) derived change-of-rings functor"]
#check @CategoryTheory.derivedTensorChangeOfRings

/- Lemma 15.60.1 (2), tag `06Y6`: this change-of-rings functor is triangulated. -/
@[stacks 06Y6 "(2) triangulated exactness"]
#check @CategoryTheory.derivedTensorChangeOfRings_isTriangulated

/- Lemma 15.60.1 (3), tag `06Y6`: objectwise, the functor factors through derived scalar
extension and the target-ring derived tensor product. -/
@[stacks 06Y6 "(3) scalar-extension factorization"]
#check @CategoryTheory.derivedTensorChangeOfRingsObjIso

#check @CategoryTheory.derivedTensorChangeOfRings_commShift
