/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Integral
public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap107.Lemma_107_5_24_Jacobson

/-!
# Integral algebraic stacks

An algebraic stack is integral when it is reduced, decent, its inertia
morphism is quasi-compact, and its space of points is irreducible. This is
strictly stronger than reduced and irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (inertia)
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Inertia.instAlgebraicStack :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    AlgebraicStack (inertia.{u + 1, u, u, u + 1} X))

#check (AlgebraicGeometry.AlgebraicStack.IsIntegral :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isIntegral_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsIntegral X ↔ IsReduced X ∧ IsDecent X ∧ IsIrreducible X ∧
      QuasiCompact (forget.{u + 1, u, u, u + 1} X))

#check (AlgebraicGeometry.AlgebraicStack.IsIntegral.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsIntegral X],
    IsReduced X ∧ IsDecent X ∧ QuasiCompact (forget.{u + 1, u, u, u + 1} X) ∧
      IsIrreducible X)

#check (AlgebraicGeometry.AlgebraicStack.IsIntegral.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsReduced X] [IsDecent X] [IsIrreducible X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)], IsIntegral X)

#check (AlgebraicGeometry.AlgebraicStack.instIsIntegral_slice :
  ∀ {S : Scheme.{u}} (U : Over S) [AlgebraicGeometry.IsIntegral U.left],
    IsIntegral (GroupoidsOver.slice U))

end AlgebraicGeometry.AlgebraicStack
