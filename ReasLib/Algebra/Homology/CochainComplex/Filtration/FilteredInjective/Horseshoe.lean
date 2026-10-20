/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Horseshoes of Filtered-Injective Complexes

This module owns the data supplied by a horseshoe construction for finite filtered objects.
It is stated in the bounded-below, termwise filtered-injective category so that applications do
not rebuild the same middle complex, lower row, and comparison diagram from an existential.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjectivePlus

/-- A termwise split filtered-injective horseshoe over a short exact sequence of finite filtered
objects. -/
@[stacks 05TV "filtered-injective horseshoe"]
structure Horseshoe
    (S : ShortComplex (FilteredObject.Finite.category C))
    {I J : FilteredInjectivePlus C}
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J) where
  /-- The middle bounded-below complex of filtered-injective objects. -/
  middle : FilteredInjectivePlus C
  /-- The horseshoe middle complex vanishes below degree zero. -/
  strictlyGE : ((FilteredInjectivePlus.ι C).obj middle).IsStrictlyGE 0
  /-- The left morphism of the lower horseshoe row. -/
  i : I ⟶ middle
  /-- The right morphism of the lower horseshoe row. -/
  p : middle ⟶ J
  /-- The lower horseshoe row is a complex. -/
  zero : i ≫ p = 0
  /-- The comparison from the degree-zero short complex to the lower horseshoe row. -/
  comparison : S.map (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)) ⟶
    (ShortComplex.mk i p zero).map (FilteredInjectivePlus.ι C)
  /-- Each degree of the lower row is split. -/
  splitting : ∀ n : ℤ,
    ((ShortComplex.mk i p zero).map
      (FilteredInjectivePlus.ι C ⋙
        HomologicalComplex.eval (FilteredObject.Finite.category C) (ComplexShape.up ℤ) n)).Splitting
  /-- The left component of the comparison is the prescribed one. -/
  comparison_left : comparison.τ₁ = a
  /-- The right component of the comparison is the prescribed one. -/
  comparison_right : comparison.τ₃ = c

/-- A horseshoe exists for prescribed degree-zero associated-graded quasi-isomorphisms from the
outer terms of a short exact sequence of finite filtered objects. -/
@[stacks 05TV "filtered-injective horseshoe"]
theorem exists_horseshoe [EnoughInjectives C]
    (S : ShortComplex (FilteredObject.Finite.category C)) (hS : S.ShortExact)
    {I J : FilteredInjectivePlus C}
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J)
    (hI : ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0)
    (hJ : ((FilteredInjectivePlus.ι C).obj J).IsStrictlyGE 0)
    (ha : FilteredObject.Finite.CochainComplex.quasiIso C a)
    (hc : FilteredObject.Finite.CochainComplex.quasiIso C c) :
    Nonempty (Horseshoe S a c) := sorry

namespace Horseshoe

/-- The short resolving row of a filtered-injective horseshoe. -/
@[stacks 05TV "filtered-injective horseshoe"]
abbrev row
    {S : ShortComplex (FilteredObject.Finite.category C)}
    {I J : FilteredInjectivePlus C}
    {a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I}
    {c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J}
    (H : Horseshoe S a c) : ShortComplex (FilteredInjectivePlus C) :=
  ShortComplex.mk H.i H.p H.zero

/-- The middle component of a filtered-injective horseshoe comparison. -/
@[stacks 05TV "filtered-injective horseshoe"]
abbrev middleComparison
    {S : ShortComplex (FilteredObject.Finite.category C)}
    {I J : FilteredInjectivePlus C}
    {a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I}
    {c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J}
    (H : Horseshoe S a c) :
    (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₂ ⟶
      (FilteredInjectivePlus.ι C).obj H.middle :=
  H.comparison.τ₂

/-- A filtered-injective horseshoe has a quasi-isomorphic middle comparison after applying the
finite associated-graded cochain functor. -/
@[stacks 05TV "filtered-injective horseshoe"]
def HasQuasiIso
    {S : ShortComplex (FilteredObject.Finite.category C)}
    {I J : FilteredInjectivePlus C}
    {a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I}
    {c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J}
    (H : Horseshoe S a c) : Prop :=
  FilteredObject.Finite.CochainComplex.quasiIso C H.middleComparison

/-- The horseshoe can be chosen with a quasi-isomorphic middle comparison whenever its outer
comparison maps are associated-graded quasi-isomorphisms. -/
@[stacks 05TV "filtered-injective horseshoe"]
theorem exists_withQuasiIso [EnoughInjectives C]
    (S : ShortComplex (FilteredObject.Finite.category C)) (hS : S.ShortExact)
    {I J : FilteredInjectivePlus C}
    (a : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₁ ⟶
      (FilteredInjectivePlus.ι C).obj I)
    (c : (CochainComplex.singleFunctor (FilteredObject.Finite.category C) (0 : ℤ)).obj S.X₃ ⟶
      (FilteredInjectivePlus.ι C).obj J)
    (hI : ((FilteredInjectivePlus.ι C).obj I).IsStrictlyGE 0)
    (hJ : ((FilteredInjectivePlus.ι C).obj J).IsStrictlyGE 0)
    (ha : FilteredObject.Finite.CochainComplex.quasiIso C a)
    (hc : FilteredObject.Finite.CochainComplex.quasiIso C c) :
    ∃ H : Horseshoe S a c, H.HasQuasiIso := sorry

end Horseshoe

end FilteredInjectivePlus

end CochainComplex
