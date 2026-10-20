/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Geometric normality as a morphism property

This file relates geometric normality for a scheme over a field to the generic
geometric form of the normal-scheme morphism property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A scheme over a field is geometrically normal exactly when its structure morphism
has the geometric form of the normal-scheme property. -/
theorem geometricallyNormal_iff_geometrically
    (X : Over (Spec (CommRingCat.of k))) :
    geometricallyNormal X ↔ geometrically Scheme.isNormal X.hom := sorry

end AlgebraicGeometry.SchemeOverField
