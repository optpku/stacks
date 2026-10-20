module

public import ReasLib.AlgebraicGeometry.NumericalType

#check (NumericalType : Type)
#check (NumericalType.of :
  ∀ (n : ℕ) (n_pos : 0 < n)
    (multiplicity weight componentGenus : Fin n → ℕ)
    (intersection : Matrix (Fin n) (Fin n) ℤ)
    (multiplicity_pos : ∀ i, 0 < multiplicity i)
    (weight_pos : ∀ i, 0 < weight i)
    (symmetric : ∀ i j, intersection i j = intersection j i)
    (offDiagonal_nonnegative : ∀ i j, i ≠ j → 0 ≤ intersection i j)
    (connected : ∀ I : Set (Fin n), I.Nonempty → I ≠ Set.univ →
      ∃ i ∈ I, ∃ j ∉ I, intersection i j ≠ 0)
    (rowSum_eq_zero : ∀ i, ∑ j, intersection i j * (multiplicity j : ℤ) = 0)
    (weight_dvd : ∀ i j, (weight i : ℤ) ∣ intersection i j),
    NumericalType)
