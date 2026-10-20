/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Cofinal ideal sheaves

This file relates containment of closed supports to containment by a positive power of an ideal
sheaf on a Noetherian scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- On a Noetherian scheme, containment of the support of `I` in that of `J` implies that a
positive power of `J` is contained in `I`. -/
theorem exists_pow_le_of_support_le {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData) (h : I.support ≤ J.support) :
    ∃ n : ℕ, 0 < n ∧ J ^ n ≤ I := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
