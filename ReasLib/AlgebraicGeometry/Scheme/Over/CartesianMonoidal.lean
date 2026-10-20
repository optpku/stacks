/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Cartesian monoidal structure on nested slices of schemes

This module supplies the canonical Cartesian monoidal structure on the slice over a
scheme over a fixed base.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The slice over an object of `Over S` has its canonical Cartesian monoidal structure. -/
noncomputable instance instCartesianMonoidalCategoryOverOver
    {S : Scheme.{u}} (U : Over S) : CartesianMonoidalCategory (Over U) :=
  Over.cartesianMonoidalCategory U

/-- The slice over an object of `Over S` has its canonical Cartesian braiding. -/
noncomputable instance instBraidedCategoryOverOver
    {S : Scheme.{u}} (U : Over S) : BraidedCategory (Over U) :=
  Over.braidedCategory U

/-- The iterated-slice equivalence carries its canonical finite-product monoidal structure. -/
noncomputable instance instMonoidalIteratedSliceForward
    {S : Scheme.{u}} (U : Over S) : U.iteratedSliceEquiv.functor.Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts _

/-- The iterated-slice equivalence carries its canonical Cartesian braiding. -/
noncomputable instance instBraidedIteratedSliceForward
    {S : Scheme.{u}} (U : Over S) : U.iteratedSliceEquiv.functor.Braided :=
  Functor.Braided.ofChosenFiniteProducts _

end AlgebraicGeometry.Scheme
