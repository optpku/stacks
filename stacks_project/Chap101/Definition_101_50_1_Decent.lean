/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Decent algebraic stacks

An algebraic stack is decent when every point is represented by a
quasi-compact morphism from the spectrum of a field. Unlike algebraic
spaces, no monomorphism hypothesis is required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsDecent :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isDecent_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsDecent X ↔ ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x)

#check (AlgebraicGeometry.AlgebraicStack.IsDecent.spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X],
    ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x)

#check (AlgebraicGeometry.AlgebraicStack.IsDecent.of :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x), IsDecent X)

#check (AlgebraicGeometry.AlgebraicStack.instIsDecent_slice :
  ∀ {S : Scheme.{u}} (U : Over S), IsDecent (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.instIsDecent_of_toGroupoids :
  ∀ {S : Scheme.{u}} (A : AlgebraicSpace S) [AlgebraicSpace.IsDecent A],
    IsDecent A.toGroupoids)

end AlgebraicGeometry.AlgebraicStack
