/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Open complements of ideal-sheaf supports

This file associates to ideal-sheaf data the open complement of its closed support.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The open complement of the support of ideal-sheaf data. -/
def openComplement (I : X.IdealSheafData) : X.Opens :=
  I.support.compl

/-- A point lies in the open complement exactly when it does not lie in the support. -/
@[simp]
theorem mem_openComplement_iff (I : X.IdealSheafData) (x : X) :
    x ∈ I.openComplement ↔ x ∉ I.support :=
  Iff.rfl

end AlgebraicGeometry.Scheme.IdealSheafData
