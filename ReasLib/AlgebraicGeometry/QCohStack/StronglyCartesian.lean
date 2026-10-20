/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.QCohStack
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.QCohStack

/-- A morphism in `QCohStack` is strongly cartesian over its underlying scheme map
if and only if its pullback map of quasi-coherent sheaves is an isomorphism. -/
theorem isStronglyCartesian_iff_isIso_sheaf {S : Scheme.{u}} {x y : Obj S} (φ : x ⟶ y) :
    (p S).IsStronglyCartesian ((p S).map φ) φ ↔ IsIso φ.sheaf :=
  sorry

end AlgebraicGeometry.QCohStack
