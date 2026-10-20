/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap101.Lemma_101_25_5_Flat

/-!
# Pullback of quasi-coherent modules along a flat morphism

If `f : X ⟶ Y` is a flat morphism of algebraic stacks, then quasi-coherent
pullback `f^* : QCoh Y ⥤ QCoh X` is an exact functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [AlgebraicStack.Flat f]

/-- Lemma 103.4.1: if `f : X ⟶ Y` is a flat morphism of algebraic stacks, then
the quasi-coherent pullback `f^* : QCoh Y ⥤ QCoh X` is an exact functor. -/
@[stacks 076X]
theorem pullback_exact : exactFunctor (QCoh Y) (QCoh X) (pullback f) :=
  sorry

/-- Quasi-coherent pullback along a flat morphism of algebraic stacks preserves
finite limits. -/
instance pullback_preservesFiniteLimits : PreservesFiniteLimits (pullback f) :=
  sorry

/-- Quasi-coherent pullback along a flat morphism of algebraic stacks preserves
finite colimits. -/
instance pullback_preservesFiniteColimits :
    PreservesFiniteColimits (pullback f) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
