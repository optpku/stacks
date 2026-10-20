/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Common geometric extensions of field-valued points

Geometric representatives of the same point of an algebraic space admit a common
extension with algebraically closed source field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Geometric points with the same image in `|X|` admit a common geometric extension. -/
theorem exists_geometric_commonExtension (p q : FieldValuedPoint X)
    [IsAlgClosed p.K] [IsAlgClosed q.K] (h : Points.mk p = Points.mk q) :
    ∃ e : CommonExtension p q, IsAlgClosed e.point.K := sorry

end AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint
