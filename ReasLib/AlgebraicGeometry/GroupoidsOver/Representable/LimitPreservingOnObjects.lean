/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Size

/-!
# Checking representability using limit preservation on objects

A 1-morphism of Zariski stacks in groupoids over `(Sch/S)_fppf` is representable
by algebraic spaces as soon as the target is limit preserving on objects and
affine locally finite presentation tests are represented by algebraic spaces of
bounded size.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor.Fiber
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.YonedaSlice
open AlgebraicSpace
open scoped Bicategory Cardinal

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism of Zariski stacks in groupoids is representable by algebraic
spaces if its target is limit preserving on objects and every fibre-object test
over an affine scheme locally of finite presentation over the base is represented
by an algebraic space of size at most the size of a fixed scheme over the base. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : Y.p.Fiber V),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f (YonedaSlice.representative y) Fy fy ∧
          sizeLE T.left.size Fy) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

/-- A morphism of Zariski stacks in groupoids is representable by algebraic
spaces if its target is limit preserving on objects and every slice test over an
affine scheme locally of finite presentation over the base is represented by an
algebraic space of size at most the size of a fixed scheme over the base. -/
theorem relativelyRepresentableByAlgebraicSpaces.of_limitPreservingOnObjects_slice
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (T : Over S)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Y)]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.zariskiTopology.over S) Y.p]
    (h : ∀ (V : Over S) [IsAffine V.left] [LocallyOfFinitePresentation V.hom]
      (y : GroupoidsOver.slice V ⟶ Y),
      ∃ (Fy : AlgebraicSpace S) (fy : Fy ⟶ ofOver V),
        RepresentsBaseChange f y Fy fy ∧ sizeLE T.left.size Fy) :
    relativelyRepresentableByAlgebraicSpaces f :=
  sorry

end AlgebraicGeometry
