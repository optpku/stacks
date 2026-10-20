/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Grp
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Symmetric invertible modules on group schemes

An invertible module is symmetric when its pullback along inversion is isomorphic to it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on a group scheme is symmetric if it is isomorphic to its
pullback along inversion. -/
def IsSymmetric {K : Type u} [Field K] (X : SchemeOverField K) [GrpObj X]
    (L : X.left.Modules) [Invertible L] : Prop :=
  Nonempty ((pullback (ι[X].left)).obj L ≅ L)

/-- Symmetry of an invertible module is existence of an isomorphism with its pullback
along inversion. -/
theorem isSymmetric_iff {K : Type u} [Field K] (X : SchemeOverField K) [GrpObj X]
    (L : X.left.Modules) [Invertible L] :
    IsSymmetric X L ↔ Nonempty ((pullback (ι[X].left)).obj L ≅ L) := sorry

end AlgebraicGeometry.Scheme.Modules
