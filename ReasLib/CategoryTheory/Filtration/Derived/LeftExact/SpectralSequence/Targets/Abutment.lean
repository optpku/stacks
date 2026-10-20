/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets.Value
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Abutment targets of finite filtered right-derived spectral sequences
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

/-- The degree-`n` abutment target, functorial in the bounded-below finite filtered complex. -/
@[stacks 015W "functorial abutment of a finite filtered right-derived spectral sequence"]
noncomputable abbrev functor (T : A ⥤ₗ B) [EnoughInjectives A] (n : ℤ) :
    CochainComplex.Plus (FilteredObject.Finite.category A) ⥤ B :=
  Underlying.functor T ⋙ DerivedCategory.Plus.homologyFunctor B n

/-- The degree-`n` abutment target attached to a bounded-below finite filtered complex. -/
@[stacks 015W "abutment target of a finite filtered right-derived spectral sequence"]
noncomputable abbrev obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) (n : ℤ) : B :=
  (DerivedCategory.Plus.homologyFunctor B n).obj (underlying T K)

/-- The abutment target map induced by a map of bounded-below finite filtered complexes. -/
@[stacks 015W "abutment map of a finite filtered right-derived spectral sequence"]
noncomputable abbrev map (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L)
    (n : ℤ) : obj T K n ⟶ obj T L n :=
  (DerivedCategory.Plus.homologyFunctor B n).map (underlyingMap T f)

/-- Object computation for the functorial abutment target. -/
@[simp, stacks 015W "functorial abutment of a finite filtered right-derived spectral sequence"]
theorem functor_obj (T : A ⥤ₗ B) [EnoughInjectives A]
    (n : ℤ) (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    (functor T n).obj K = obj T K n := sorry

/-- Morphism computation for the functorial abutment target. -/
@[simp, stacks 015W "functorial abutment of a finite filtered right-derived spectral sequence"]
theorem functor_map (T : A ⥤ₗ B) [EnoughInjectives A]
    (n : ℤ) {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    (functor T n).map f = map T f n := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment
