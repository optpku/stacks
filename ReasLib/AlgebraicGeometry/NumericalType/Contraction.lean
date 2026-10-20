/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType
public import ReasLib.AlgebraicGeometry.NumericalType.MinusOneIndex
public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import Mathlib.Algebra.Ring.Int.Parity

@[expose] public section

namespace NumericalType

/-- Contract a numerical type along a chosen final `(-1)`-index. -/
public def contractMinusOne (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) : NumericalType :=
  let k : Fin T.n := e (Fin.last (T.n - 1))
  let w' : Fin (T.n - 1) → ℕ := fun i ↦
    if Even (T.intersection (e i.castSucc) k / (T.weight k : ℤ)) ∧
        Odd (T.intersection (e i.castSucc) k /
          (T.weight (e i.castSucc) : ℤ)) then
      T.weight (e i.castSucc) / 2
    else
      T.weight (e i.castSucc)
  let a' : Matrix (Fin (T.n - 1)) (Fin (T.n - 1)) ℤ := fun i j ↦
    T.intersection (e i.castSucc) (e j.castSucc) -
      T.intersection (e i.castSucc) k * T.intersection (e j.castSucc) k /
        T.intersection k k
  let g' : Fin (T.n - 1) → ℕ := fun i ↦
    Int.toNat <|
      ((T.weight (e i.castSucc) : ℤ) / (w' i : ℤ)) *
          ((T.componentGenus (e i.castSucc) : ℤ) - 1) + 1 +
        (T.intersection (e i.castSucc) k ^ 2 -
            (T.weight k : ℤ) * T.intersection (e i.castSucc) k) /
          (2 * (w' i : ℤ) * (T.weight k : ℤ))
  { n := T.n - 1
    n_pos := sorry
    multiplicity := fun i ↦ T.multiplicity (e i.castSucc)
    intersection := a'
    weight := w'
    componentGenus := g'
    multiplicity_pos := sorry
    weight_pos := sorry
    symmetric := sorry
    offDiagonal_nonnegative := sorry
    connected := sorry
    rowSum_eq_zero := sorry
    weight_dvd := sorry }


/-- Contracting a numerical type along a chosen `(-1)`-index decreases its number of indices by one. -/
public theorem contractMinusOne_n (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) :
    (contractMinusOne T e hminus).n = T.n - 1 := sorry

/-- Contraction preserves the multiplicities at the retained indices. -/
public theorem contractMinusOne_multiplicity (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)) :
    (contractMinusOne T e hminus).multiplicity i = T.multiplicity (e i.castSucc) := sorry

/-- The intersection matrix of a contracted numerical type is the Schur complement of the exceptional diagonal entry. -/
public theorem contractMinusOne_intersection (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i j : Fin (T.n - 1)) :
    (contractMinusOne T e hminus).intersection i j =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
            T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
          T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1))) := sorry

/-- A retained weight is halved precisely when its intersection with the exceptional index divided by the exceptional weight is even and divided by the retained weight is odd. -/
public theorem contractMinusOne_weight (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)) :
    (contractMinusOne T e hminus).weight i =
      if Even (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) /
          (T.weight (e (Fin.last (T.n - 1))) : ℤ)) ∧
          Odd (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) /
            (T.weight (e i.castSucc) : ℤ)) then
        T.weight (e i.castSucc) / 2
      else
        T.weight (e i.castSucc) := sorry

/-- The component genus after contraction is given by the integer formula involving the retained weight, exceptional weight, and exceptional intersection. -/
public theorem contractMinusOne_componentGenus (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)) :
    ((contractMinusOne T e hminus).componentGenus i : ℤ) =
      ((T.weight (e i.castSucc) : ℤ) /
          ((contractMinusOne T e hminus).weight i : ℤ)) *
          ((T.componentGenus (e i.castSucc) : ℤ) - 1) + 1 +
        (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) ^ 2 -
            (T.weight (e (Fin.last (T.n - 1))) : ℤ) *
              T.intersection (e i.castSucc) (e (Fin.last (T.n - 1)))) /
          (2 * ((contractMinusOne T e hminus).weight i : ℤ) *
            (T.weight (e (Fin.last (T.n - 1))) : ℤ)) := sorry

/-- Contracting a numerical type along a `(-1)`-index preserves its total genus. -/
public theorem contractMinusOne_genus (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) :
    T.genus = (contractMinusOne T e hminus).genus := sorry

end NumericalType

end
