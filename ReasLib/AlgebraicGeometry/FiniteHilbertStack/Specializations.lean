/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.GroupoidsBase
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Stack

/-!
# Absolute finite Hilbert stacks

The finite Hilbert stack specializes along the structure morphism of a stack
and along the identity morphism of the base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

/-- The degree `d` finite Hilbert stack of `X` over its base scheme. -/
abbrev ofStack {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (baseProjection.{u + 1, u, u + 1} X) d

/-- `ofStack X d` is the finite Hilbert stack of the structure 1-morphism of `X`. -/
theorem ofStack_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    ofStack X d = stack (baseProjection.{u + 1, u, u + 1} X) d :=
  rfl

/-- The projection of `ofStack X d` is the forgetful functor of the structure
1-morphism. -/
theorem ofStack_p {S : Scheme.{u}} (X : GroupoidsOver S)
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p] (d : ℕ) :
    (ofStack X d).p = p (baseProjection.{u + 1, u, u + 1} X) d :=
  rfl

/-- The degree `d` finite Hilbert stack of the base scheme over itself. -/
abbrev ofScheme (S : Scheme.{u}) (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  stack (𝟙 (base.{u + 1, u, u + 1} (Over S))) d

/-- `ofScheme S d` is the finite Hilbert stack of the identity 1-morphism of `S`. -/
theorem ofScheme_eq (S : Scheme.{u}) (d : ℕ) :
    ofScheme S d = stack (𝟙 (base.{u + 1, u, u + 1} (Over S))) d :=
  rfl

/-- The projection of `ofScheme S d` is the forgetful functor of the identity
1-morphism of `S`. -/
theorem ofScheme_p (S : Scheme.{u}) (d : ℕ) :
    (ofScheme S d).p = p (𝟙 (base.{u + 1, u, u + 1} (Over S))) d :=
  rfl

end AlgebraicGeometry.FiniteHilbertStack
