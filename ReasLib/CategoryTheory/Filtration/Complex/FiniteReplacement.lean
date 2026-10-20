/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.StrictReplacement
public import ReasLib.CategoryTheory.Filtration.Complex.FiniteCategory
public import ReasLib.CategoryTheory.GradedObject.Homology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict Filtered-Injective Replacements

This module states the reusable bounded-below replacement theorem for finite filtered complexes.
The finite-complex formulation is primary; the termwise-finite bridge retains the common input
shape used by filtered-complex applications.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]

namespace StrictReplacement

/-- A bounded-below complex of finite filtered objects admits a termwise strict monomorphic
filtered quasi-isomorphism to a bounded-below complex of filtered-injective objects. -/
@[stacks 05TW "strict filtered-injective replacement"]
theorem exists_of_finiteComplex (a : ℤ)
    (K : FilteredObject.Finite.CochainComplex A) (hK : K.IsStrictlyGE a) :
    ∃ (I : CochainComplex.FilteredInjectivePlus A) (f : K ⟶ I),
      _root_.CochainComplex.FilteredReplacement.IsStrict
        (FilteredObject.Finite.inclusion A)
        (FilteredObject.Finite.AssociatedGraded.functor A)
        (FilteredObject.Finite.FilteredInjective.property A) a I f := sorry

/-- A bounded-below filtered complex with termwise finite filtrations admits a termwise strict
monomorphic filtered quasi-isomorphism to a bounded-below filtered-injective complex. -/
@[stacks 05TW "strict filtered-injective replacement"]
theorem exists_of_finiteFiltrations (a : ℤ)
    (K : FilteredComplex A) (hK : K.underlying.IsStrictlyGE a)
    (hKfin : K.HasFiniteFiltrations) :
    ∃ (I : CochainComplex.FilteredInjectivePlus A)
      (f : K ⟶ (FilteredObject.Finite.CochainComplex.inclusion A).obj I),
      _root_.CochainComplex.FilteredReplacement.IsStrict
        (FilteredObject.Finite.inclusion A)
        (FilteredObject.Finite.AssociatedGraded.functor A)
        (FilteredObject.Finite.FilteredInjective.property A) a I
          (Finite.liftMapTo hKfin f) := sorry

end StrictReplacement

end FilteredComplex

end CategoryTheory
