/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Value
public import Mathlib.Tactic.CrossRefAttribute

/-!
# First-page targets of finite filtered right-derived spectral sequences
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.PageOne

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The `(p, q)` first-page target, functorial in the bounded-below finite filtered complex. -/
@[stacks 015W "functorial first page of a finite filtered right-derived spectral sequence"]
noncomputable abbrev functor (T : A ⥤ₗ B) [EnoughInjectives A] (p q : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category A) ⥤ B :=
  GradedPiece.functor T p ⋙ DerivedCategory.Plus.homologyFunctor B (p + q)

/-- The `(p, q)` first-page target attached to a bounded-below finite filtered complex. -/
@[stacks 015W "first-page target of a finite filtered right-derived spectral sequence"]
noncomputable abbrev obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (p q : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).obj (gradedPiece T K p)

/-- The first-page target map induced by a map of bounded-below finite filtered complexes. -/
@[stacks 015W "first-page map of a finite filtered right-derived spectral sequence"]
noncomputable abbrev map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L)
    (p q : ℤ) : obj T K p q ⟶ obj T L p q :=
  (DerivedCategory.Plus.homologyFunctor B (p + q)).map (gradedPieceMap T f p)

/-- Object computation for the functorial first-page target. -/
@[simp, stacks 015W "functorial first page of a finite filtered right-derived spectral sequence"]
theorem functor_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (p q : ℤ) (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    (functor T p q).obj K = obj T K p q := sorry

/-- Morphism computation for the functorial first-page target. -/
@[simp, stacks 015W "functorial first page of a finite filtered right-derived spectral sequence"]
theorem functor_map (T : A ⥤ₗ B) [EnoughInjectives A]
    (p q : ℤ) {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    (functor T p q).map f = map T f p q := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.PageOne
