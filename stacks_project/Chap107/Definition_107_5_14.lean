/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 107.5.14: a locally Noetherian algebraic stack `X` is
pseudo-catenary if there exists a smooth and surjective morphism `U ⟶ X`
whose source is a universally catenary scheme. -/
@[stacks 0DRU] #check (AlgebraicGeometry.AlgebraicStack.IsPseudoCatenary :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.isPseudoCatenary_iff_existsSurjectiveSmooth :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X],
    AlgebraicGeometry.AlgebraicStack.IsPseudoCatenary X ↔
      AlgebraicGeometry.AlgebraicStack.existsSurjectiveSmooth
        (AlgebraicGeometry.UniversallyCatenary :
          CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u}) X)
