module

public import ReasLib.AlgebraicGeometry.NumericalType.MinusTwoIndex

@[expose] public section

namespace NumericalType

#check (NumericalType.IsMinusTwoIndex :
  {n : ℕ} → (Fin n → ℕ) → (Fin n → ℕ) →
    Matrix (Fin n) (Fin n) ℤ → Fin n → Prop)

#check (NumericalType.IsMinusTwoIndex.ofEquations :
  {n : ℕ} → {componentGenus weight : Fin n → ℕ} →
    {intersection : Matrix (Fin n) (Fin n) ℤ} → {i : Fin n} →
    componentGenus i = 0 →
    intersection i i = (-2 : ℤ) * weight i →
    NumericalType.IsMinusTwoIndex componentGenus weight intersection i)

#check (NumericalType.IsMinusTwoIndex.reindex_iff :
  {n : ℕ} → (componentGenus weight : Fin n → ℕ) →
    (intersection : Matrix (Fin n) (Fin n) ℤ) →
    (e : Equiv.Perm (Fin n)) → (i : Fin n) →
    NumericalType.IsMinusTwoIndex (componentGenus ∘ e)
        (weight ∘ e) (intersection.submatrix e e) i ↔
      NumericalType.IsMinusTwoIndex componentGenus weight intersection (e i))

end NumericalType
