/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a morphism of finite presentation, the projection from finitely presented modules
on scheme-valued fibers, flat with proper support over the test scheme, is a stack in
groupoids for the fppf topology. -/
@[stacks 08KC]
instance instIsStackInGroupoids (f : X ⟶ B) [FinitePresentation f] :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
