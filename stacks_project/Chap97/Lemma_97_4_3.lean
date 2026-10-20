/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.FlatAtlas
import StacksCheckRecall

/-!
# Diagonals of stacks with an fppf algebraic-space atlas

If a stack in groupoids over `(Sch/S)_fppf` admits a 1-morphism from an
algebraic space that is representable by algebraic spaces, surjective, flat,
and locally of finite presentation, then its diagonal is representable by
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

/- Lemma 97.4.3: Let `S` be a scheme. Let `u : U ⟶ X` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `U` is representable by an
algebraic space, and `u` is representable by algebraic spaces, surjective,
flat, and locally of finite presentation, then `Δ : X ⟶ X × X` is
representable by algebraic spaces. -/
@[stacks 05XW] #check
  (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_of_fppfAtlas :
    ∀ {S : Scheme.{u}} {U X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) U.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (u : U ⟶ X) (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Surjective u] [Groupoids.Hom.Flat u]
    [Groupoids.Hom.LocallyOfFinitePresentation u],
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
