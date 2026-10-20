/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Basic
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Basic
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finite Hilbert stacks

Finite locally free lifts along a morphism of stacks in groupoids satisfy
fppf descent, in every natural rank.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- The category of finite locally free degree-`d` lifts of a morphism of stacks
in groupoids is a stack over the big fppf site. This holds also for rank zero:
affine effectivity and descent of finite local freeness require no positivity. -/
instance isStackInGroupoids
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p F d) := sorry

/-- For positive rank, finite Hilbert lifts of a morphism of stacks in groupoids
form a stack in groupoids over the big fppf site. -/
theorem isStackInGroupoids_of_pos
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) (hd : 1 ≤ d) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p F d) :=
  isStackInGroupoids F d

/-- The stack in groupoids of degree `d` finite Hilbert lifts along `F`. -/
def stack
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  StackOver.Groupoids.ofProjection (Scheme.fppfTopology.over S) (p F d)

/-- The projection of `stack` is the forgetful functor `p`. -/
theorem stack_p
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (d : ℕ) :
    (stack F d).p = p F d := rfl

end AlgebraicGeometry.FiniteHilbertStack
