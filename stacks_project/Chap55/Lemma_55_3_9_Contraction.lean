/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Contraction

/- Contraction of a numerical type along a chosen final `(-1)`-index. -/
#check (NumericalType.contractMinusOne :
  ∀ (T : NumericalType) (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : NumericalType.IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))), NumericalType)
