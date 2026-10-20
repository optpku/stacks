/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation

/-!
# Diagonals of stacks with an fppf algebraic-space atlas

A stack admitting a representable, surjective, flat, locally finitely presented
morphism from an algebraic-space-representable stack has representable diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If a stack in groupoids over `(Sch/S)_fppf` admits a representable,
surjective, flat, locally finitely presented morphism from a stack representable
by an algebraic space, then its diagonal is representable by algebraic spaces. -/
@[stacks 05XW]
theorem relativelyRepresentableByAlgebraicSpaces.diagonal_of_fppfAtlas
    {S : Scheme.{u}} {U X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) U.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (u : U ⟶ X) (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective u] [Groupoids.Hom.Flat u]
    [Groupoids.Hom.LocallyOfFinitePresentation u] :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry
