/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Irreducible
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.JacobsonSpace
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Jacobson and irreducible algebraic stacks

An algebraic stack is Jacobson when it admits a surjective smooth atlas from a
Jacobson scheme. It is irreducible when every canonical topology on its points
is an irreducible space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.IsJacobson :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isJacobson_iff :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsJacobson X ↔ ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧ JacobsonSpace U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsJacobson.spec :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsJacobson X],
    ∃ (U : Over S) (p : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        JacobsonSpace U.left)

#check (AlgebraicGeometry.AlgebraicStack.IsJacobson.of :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [JacobsonSpace U.left],
    IsJacobson X)

#check (AlgebraicGeometry.AlgebraicStack.instIsJacobson_slice :
    ∀ {S : Scheme.{u}} (U : Over S) [JacobsonSpace U.left],
      IsJacobson (GroupoidsOver.slice U))

#check (AlgebraicGeometry.AlgebraicStack.isJacobson_iff_existsSurjectiveSmooth :
    ∀ {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X],
    IsJacobson X ↔
      existsSurjectiveSmooth (fun U : Scheme.{u} ↦ JacobsonSpace U) X)

#check (AlgebraicGeometry.AlgebraicStack.IsIrreducible :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isIrreducible_iff :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsIrreducible X ↔ ∀ (τ : TopologicalSpace (Points X)),
        IsPointsTopology X τ → @IrreducibleSpace (Points X) τ)

#check (AlgebraicGeometry.AlgebraicStack.IsIrreducible.spec :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIrreducible X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ),
    @IrreducibleSpace (Points X) τ)

#check (AlgebraicGeometry.AlgebraicStack.IsIrreducible.of :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ),
    IsIrreducible X)

#check (AlgebraicGeometry.AlgebraicStack.instIsIrreducible_slice :
    ∀ {S : Scheme.{u}} (U : Over S) [IrreducibleSpace U.left],
      IsIrreducible (GroupoidsOver.slice U))

end AlgebraicGeometry.AlgebraicStack
