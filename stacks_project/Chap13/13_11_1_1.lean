/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import StacksCheckRecall

@[expose] public section
open CategoryTheory CategoryTheory.Pretriangulated
noncomputable section

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (T : Triangle (DerivedCategory C))
variable (hT : T ∈ distTriang _) (i : ℤ)

/- 13.11.1.1: every distinguished triangle in D(C) gives an exact cohomology sequence.
The third arrow is the canonical shifted image of the triangle's connecting morphism;
the six-term windows for all i supply every adjacent exactness position. -/
@[stacks 05ST] #check
  (CategoryTheory.Functor.homologySequenceComposableArrows₅_exact
      (DerivedCategory.homologyFunctor C 0) T hT i (i + 1) rfl :
    (CategoryTheory.Functor.homologySequenceComposableArrows₅
      (DerivedCategory.homologyFunctor C 0) T i (i + 1) rfl).Exact)
