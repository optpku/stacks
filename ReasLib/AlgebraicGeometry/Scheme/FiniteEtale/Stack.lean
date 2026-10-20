/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Covers
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The fppf stack of finite étale covers

The target projection of finite étale arrows over a scheme is a stack on its fppf site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The target projection of finite étale morphisms over `S` is a stack on the fppf site. -/
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
