/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Contraction

namespace NumericalType

/- Lemma 55.3.9 (1): the contraction has one fewer index. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_n :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))),
    (contractMinusOne T e hminus).n = T.n - 1)

/- Lemma 55.3.9 (2): Contraction preserves the multiplicities at the retained indices. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_multiplicity :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)),
    (contractMinusOne T e hminus).multiplicity i = T.multiplicity (e i.castSucc))

/- Lemma 55.3.9 (3): The intersection matrix of a contracted numerical type is the Schur complement of the exceptional diagonal entry. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_intersection :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i j : Fin (T.n - 1)),
    (contractMinusOne T e hminus).intersection i j =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
            T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
          T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1))))

/- Lemma 55.3.9 (4): A retained weight is halved precisely when its intersection with the exceptional index divided by the exceptional weight is even and divided by the retained weight is odd. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_weight :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)),
    (contractMinusOne T e hminus).weight i =
      if Even (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) /
          (T.weight (e (Fin.last (T.n - 1))) : ℤ)) ∧
          Odd (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) /
            (T.weight (e i.castSucc) : ℤ)) then
        T.weight (e i.castSucc) / 2
      else
        T.weight (e i.castSucc))

/- Lemma 55.3.9 (5): The component genus after contraction is given by the integer formula involving the retained weight, exceptional weight, and exceptional intersection. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_componentGenus :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)),
    ((contractMinusOne T e hminus).componentGenus i : ℤ) =
      ((T.weight (e i.castSucc) : ℤ) /
          ((contractMinusOne T e hminus).weight i : ℤ)) *
          ((T.componentGenus (e i.castSucc) : ℤ) - 1) + 1 +
        (T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) ^ 2 -
            (T.weight (e (Fin.last (T.n - 1))) : ℤ) *
              T.intersection (e i.castSucc) (e (Fin.last (T.n - 1)))) /
          (2 * ((contractMinusOne T e hminus).weight i : ℤ) *
            (T.weight (e (Fin.last (T.n - 1))) : ℤ)))

/- Lemma 55.3.9 (6): Contracting a numerical type along a `(-1)`-index preserves its total genus. -/
@[stacks 0C77] #check (NumericalType.contractMinusOne_genus :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))),
    T.genus = (contractMinusOne T e hminus).genus)

end NumericalType
