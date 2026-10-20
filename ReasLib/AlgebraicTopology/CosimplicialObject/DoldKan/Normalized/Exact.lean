/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.Normalized.Equivalence
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of normalized cochains

The quotient-defined normalized cochain functor is the forward functor of the canonical
cosimplicial Dold--Kan equivalence. This leaf registers that equivalence with typeclass search and
packages the functor as a bundled exact functor.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.normalizedCochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The quotient-defined normalized cochain functor is an equivalence of categories. -/
@[stacks 019I "normalized cochain functor is an equivalence"]
instance functor.isEquivalence :
    (normalizedCochainComplex.functor (A := A)).IsEquivalence := sorry

/-- The quotient-defined normalized cochain complex, bundled as an exact functor. -/
@[stacks 019I "bundled exact normalized cochain complex"]
noncomputable def exactFunctor :
    CosimplicialObject A ⥤ₑ CochainComplex A ℕ :=
  ExactFunctor.of normalizedCochainComplex.functor

end CategoryTheory.CosimplicialObject.normalizedCochainComplex
