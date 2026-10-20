/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Composition
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Adjointification
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Choice
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift
public import ReasLib.CategoryTheory.Functor.Equivalence.Choice
public import ReasLib.CategoryTheory.Functor.Equivalence.IsEquivalence.OfFaithful

/-!
# Explicit quasi-inverses and functor equivalences

This aggregate exposes explicit quasi-inverse data, its composition, inverse-choice, and lift
APIs, choice bridges from `Functor.IsEquivalence`, and the faithful-functor equivalence criterion.
-/
