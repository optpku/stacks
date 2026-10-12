/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.MinusOneIndex

@[expose] public section

namespace NumericalType

#check (NumericalType.IsMinusOneIndex :
  ∀ {n : ℕ}, (Fin n → ℕ) → (Fin n → ℕ) → Matrix (Fin n) (Fin n) ℤ → Fin n → Prop)

#check (NumericalType.IsMinusOneIndex.ofEquations :
  ∀ {n : ℕ} {componentGenus weight : Fin n → ℕ}
    {intersection : Matrix (Fin n) (Fin n) ℤ} {i : Fin n},
    componentGenus i = 0 →
      intersection i i = -(weight i : ℤ) →
        NumericalType.IsMinusOneIndex componentGenus weight intersection i)

#check (NumericalType.IsMinusOneIndex.reindex_iff :
  ∀ {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (e : Equiv.Perm (Fin n)) (i : Fin n),
    NumericalType.IsMinusOneIndex (componentGenus ∘ e) (weight ∘ e)
        (intersection.submatrix e e) i ↔
      NumericalType.IsMinusOneIndex componentGenus weight intersection (e i))

#check (NumericalType.isMinusOneIndex_iff :
  ∀ {n : ℕ} (componentGenus weight : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ) (i : Fin n),
    NumericalType.IsMinusOneIndex componentGenus weight intersection i ↔
      componentGenus i = 0 ∧ intersection i i = -(weight i : ℤ))

end NumericalType
