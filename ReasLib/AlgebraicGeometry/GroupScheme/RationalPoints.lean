/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Rational points of group schemes
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The additive group of `k`-rational points of a group scheme over `k`. -/
abbrev rationalPoints (A : SchemeOverField k) [GrpObj A] :=
  Additive (𝟙_ (SchemeOverField k) ⟶ A)

end AlgebraicGeometry.SchemeOverField
