module

public import ReasLib.AlgebraicGeometry.NumericalType.Picard

/- The source-facing Picard API is provided by the shared numerical-type owner. -/
#check (NumericalType.picardMatrix :
  (T : NumericalType) → Matrix (Fin T.n) (Fin T.n) ℤ)
#check (NumericalType.picardMatrix_apply :
  ∀ (T : NumericalType) (i j : Fin T.n),
    T.picardMatrix i j = T.intersection i j / (T.weight i : ℤ))
#check (NumericalType.weight_mul_picardMatrix :
  ∀ (T : NumericalType) (i j : Fin T.n),
    (T.weight i : ℤ) * T.picardMatrix i j = T.intersection i j)
#check (NumericalType.picardMap :
  (T : NumericalType) → (Fin T.n → ℤ) →ₗ[ℤ] (Fin T.n → ℤ))
#check (NumericalType.picardMap_apply :
  ∀ (T : NumericalType) (x : Fin T.n → ℤ) (j : Fin T.n),
    T.picardMap x j = ∑ i, (T.intersection j i / (T.weight j : ℤ)) * x i)
#check (NumericalType.picardMap_single :
  ∀ (T : NumericalType) (i j : Fin T.n),
    T.picardMap (Pi.single i 1) j = T.intersection i j / (T.weight j : ℤ))
#check (NumericalType.PicardGroup : (T : NumericalType) → Type)
#check (NumericalType.picardGroup_eq_quotient :
  ∀ T : NumericalType,
    T.PicardGroup = ((Fin T.n → ℤ) ⧸ LinearMap.range T.picardMap))
#check (NumericalType.toPicardGroup :
  (T : NumericalType) → (Fin T.n → ℤ) →ₗ[ℤ] T.PicardGroup)
#check (NumericalType.toPicardGroup_apply :
  ∀ (T : NumericalType) (x : Fin T.n → ℤ),
    T.toPicardGroup x = (LinearMap.range T.picardMap).mkQ x)
#check (NumericalType.picardMap_toPicardGroup :
  ∀ T : NumericalType, T.toPicardGroup.comp T.picardMap = 0)
#check (NumericalType.picardGroup_exact :
  ∀ T : NumericalType, Function.Exact T.picardMap T.toPicardGroup)
#check (NumericalType.toPicardGroup_surjective :
  ∀ T : NumericalType, Function.Surjective T.toPicardGroup)
