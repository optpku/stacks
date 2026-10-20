/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Depth

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme is Cohen-Macaulay if and only if it satisfies Serre's condition
`(S_k)` for every natural number `k`. -/
theorem cohenMacaulay_iff_forall_satisfiesSerreConditionS :
    CohenMacaulay X ↔ ∀ k : ℕ, satisfiesSerreConditionS X k := sorry

end AlgebraicGeometry.Scheme
