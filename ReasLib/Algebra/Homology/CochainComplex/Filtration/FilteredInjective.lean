/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.CategoryTheory.Filtration.FiniteInjective
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Complexes of Finite Filtered-Injectives

This module specializes the property-neutral bounded-below complex API to finite filtered objects
whose associated graded pieces are injective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

/-- The bounded-below cochain complexes of finite filtered objects whose terms are filtered
injective. -/
@[stacks 015P "bounded-below finite filtered-injective complexes"]
noncomputable abbrev FilteredInjectivePlus (A : Type u) [Category.{v} A] [Abelian A] :=
  _root_.CochainComplex.Plus.TermsIn
    (_root_.CategoryTheory.FilteredObject.Finite.FilteredInjective.property A)

/-- The inclusion of bounded-below termwise filtered-injective complexes into all complexes of
finite filtered objects. -/
@[stacks 015P "inclusion of bounded-below finite filtered-injective complexes"]
noncomputable abbrev FilteredInjectivePlus.ι (A : Type u) [Category.{v} A] [Abelian A] :
    FilteredInjectivePlus A ⥤ _root_.CochainComplex (FilteredObject.Finite.category A) ℤ :=
  _root_.CochainComplex.Plus.TermsIn.ι
    (_root_.CategoryTheory.FilteredObject.Finite.FilteredInjective.property A)

end CochainComplex
