/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.QuasiCompact

/-!
# Quasi-compact field-valued points of an algebraic stack

The quasi-compactness predicate and the existential and universal representative
conditions are provided by their shared mathematical owner.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

#check (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.quasiCompact :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}, FieldValuedPoint X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.existsQuasiCompactFieldValuedPoint :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Points X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.forallFieldValuedPointQuasiCompact :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Points X → Prop)
