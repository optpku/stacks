/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Map.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence and independence for finite filtered right-derived spectral sequences

This file is a reusable leaf of the finite filtered right-derived spectral-sequence API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace Realization

/-- Any supplied comparison between two finite right-derived realizations may be chosen to be
an isomorphism from the first page onward.  Existence is explicit because compatibility of the
selected model comparisons is part of the realization-map data. -/
@[stacks 015W "independence of a finite filtered right-derived spectral sequence"]
theorem existsIsoFromOne {T : A ⥤ₗ B} [EnoughInjectives A]
    {K : CochainComplex.Plus (FilteredObject.Finite.category A)}
    (S R : Realization T K) (h : Nonempty (Map (𝟙 K) S R)) :
    ∃ m : Map (𝟙 K) S R, m.sequenceMap.IsIsoFrom 1 zero_le_one := sorry

end Realization

/-- Lemma 13.26.14 (`015W`): a left-exact functor on an abelian category with enough injectives
gives, for every bounded-below complex of finite filtered objects, a bounded cohomological
spectral sequence whose first page is the cohomology of the derived graded pieces. It converges
to the derived value of the underlying complex and induces finite filtrations on its cohomology. -/
@[stacks 015W]
theorem existsSpectralSequence (T : A ⥤ₗ B) [EnoughInjectives A]
    (K : CochainComplex.Plus (FilteredObject.Finite.category A)) :
    Nonempty (Realization T K) := sorry

/-- Functorial form of Lemma 13.26.14: a map of bounded-below finite filtered complexes admits
compatible choices of the two spectral sequences, with the expected map on the first page and on
the abutment. -/
@[stacks 015W "functoriality"]
theorem existsMap (T : A ⥤ₗ B) [EnoughInjectives A]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category A)} (f : K ⟶ L) :
    ∃ (S : Realization T K) (R : Realization T L), Nonempty (Realization.Map f S R) := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
