module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus

#check (NumericalType.genus : NumericalType → ℤ)
#check (NumericalType.genus_def : ∀ T : NumericalType,
    T.genus =
      1 + ∑ i, (T.multiplicity i : ℤ) * (T.weight i : ℤ) *
          ((T.componentGenus i : ℤ) - 1) -
        (∑ i, (T.multiplicity i : ℤ) * T.intersection i i) / 2)
#check (NumericalType.genus_cast : ∀ T : NumericalType,
    (T.genus : ℚ) =
      1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2))
#check (NumericalType.genus_eq_iff : ∀ (T : NumericalType) (g : ℤ),
    T.genus = g ↔
      (g : ℚ) = 1 + ∑ i, (T.multiplicity i : ℚ) *
        ((T.weight i : ℚ) * ((T.componentGenus i : ℚ) - 1) -
          (T.intersection i i : ℚ) / 2))
#check (NumericalType.IsRelabeling.genus_eq : ∀ {T T' : NumericalType}
    {e : Fin T.n ≃ Fin T'.n}, NumericalType.IsRelabeling T T' e →
      T.genus = T'.genus)
