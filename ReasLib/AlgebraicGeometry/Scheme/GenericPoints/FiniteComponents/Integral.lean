/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

/-!
# Finite components of integral schemes

Integral schemes have finitely many irreducible components on every quasi-compact open.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- An integral scheme has finitely many irreducible components on every quasi-compact open. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpensOfIsIntegral (X : Scheme.{u})
    [IsIntegral X] : HasFiniteIrreducibleComponentsOnCompactOpens X := sorry

end AlgebraicGeometry.Scheme
