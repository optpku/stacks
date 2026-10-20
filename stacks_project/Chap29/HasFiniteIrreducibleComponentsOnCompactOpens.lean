/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

@[expose] public section

/-!
# Finite Irreducible Components On Compact Opens

The reusable component-finiteness condition is maintained in
`ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents`.
-/

/- Every quasi-compact open subscheme has finitely many irreducible
components. -/
#check AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
#check AlgebraicGeometry.Scheme.instFiniteIrreducibleComponentsCompactOpens
