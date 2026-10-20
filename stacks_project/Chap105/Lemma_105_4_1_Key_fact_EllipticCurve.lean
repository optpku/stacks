/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.Family

/-! Compatibility view of the shared scheme-theoretic elliptic-curve API. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/- The shared predicate for scheme-theoretic elliptic curves. -/
#check (AlgebraicGeometry.EllipticCurve.IsEllipticCurve :
  ∀ {S : Scheme.{u}} (E : Over S) (zero : S ⟶ E.left), Prop)
