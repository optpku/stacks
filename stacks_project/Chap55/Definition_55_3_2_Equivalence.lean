module

public import ReasLib.AlgebraicGeometry.NumericalType.Equivalence

#check (NumericalType.IsRelabeling :
  ∀ T T' : NumericalType, (Fin T.n ≃ Fin T'.n) → Prop)
#check NumericalType.IsRelabeling.of
#check NumericalType.IsRelabeling.refl
#check (NumericalType.Equivalent : NumericalType → NumericalType → Prop)
#check NumericalType.equivalent_iff_exists_relabeling
#check NumericalType.equivalent_refl
#check NumericalType.equivalent_symm
#check NumericalType.equivalent_trans
#check NumericalType.setoid
#check NumericalType.setoid_rel
