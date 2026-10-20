/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_Restrict»

/-!
# Limit preserving on objects

The descent-problem predicate and the solution theorem for directed affine inverse limits.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.Problem.HasSolution :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I}, Problem p D c i → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [LimitPreservingOnObjects p] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ (i : I) (prob : Problem p D c i), ∃ cand : Candidate prob, IsSolution cand)
