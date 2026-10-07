module

public import ReasLib.AlgebraicGeometry.NumericalType.Contraction
public import ReasLib.AlgebraicGeometry.NumericalType.Picard
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

namespace NumericalType

/-- The rational genus expression for a surviving component with specified weight. -/
def contractionGenus (T : NumericalType) (i k : Fin T.n) (w : ℕ) : ℚ :=
  (T.weight i : ℚ) / (w : ℚ) * ((T.componentGenus i : ℚ) - 1) + 1 +
    ((T.intersection i k : ℚ) ^ 2 - (T.weight k : ℚ) * (T.intersection i k : ℚ)) /
      (2 * (w : ℚ) * (T.weight k : ℚ))

/-- The rational genus expression is not a truncating integer quotient. -/
theorem contractionGenus_eq (T : NumericalType) (i k : Fin T.n) (w : ℕ) :
    contractionGenus T i k w =
      (T.weight i : ℚ) / (w : ℚ) * ((T.componentGenus i : ℚ) - 1) + 1 +
        ((T.intersection i k : ℚ) ^ 2 - (T.weight k : ℚ) * (T.intersection i k : ℚ)) /
          (2 * (w : ℚ) * (T.weight k : ℚ)) := rfl

/-- The numerical contraction chooses the greatest positive divisor giving integral genus. -/
theorem contractMinusOne_weight_isGreatest (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)) :
    IsGreatest {w : ℕ | 0 < w ∧ w ∣ T.weight (e i.castSucc) ∧
      ∃ g : ℤ, contractionGenus T (e i.castSucc) (e (Fin.last (T.n - 1))) w = (g : ℚ)}
      ((contractMinusOne T e hminus).weight i) := sorry

/-- The computed natural genus agrees exactly with the rational contraction formula. -/
theorem contractMinusOne_genus_rational (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)) :
    ((contractMinusOne T e hminus).componentGenus i : ℚ) =
      contractionGenus T (e i.castSucc) (e (Fin.last (T.n - 1)))
        ((contractMinusOne T e hminus).weight i) := sorry

/-- The integral coordinate map inducing Picard comparison for any dividing retained weights. -/
def contractionCoordinates (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin U.n → ℤ) :=
  LinearMap.pi fun j ↦
    ((T.weight (e (f.symm j).castSucc) : ℤ) / (U.weight j : ℤ)) •
        LinearMap.proj (e (f.symm j).castSucc) +
      (T.intersection (e (Fin.last (T.n - 1))) (e (f.symm j).castSucc) /
        (U.weight j : ℤ)) • LinearMap.proj (e (Fin.last (T.n - 1)))

/-- The comparison on vectors is given by the two-term coordinate formula. -/
theorem contractionCoordinates_apply (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (v : Fin T.n → ℤ) (j : Fin U.n) :
    contractionCoordinates T U e f v j =
      (T.weight (e (f.symm j).castSucc) : ℤ) / (U.weight j : ℤ) *
          v (e (f.symm j).castSucc) +
        T.intersection (e (Fin.last (T.n - 1))) (e (f.symm j).castSucc) /
          (U.weight j : ℤ) * v (e (Fin.last (T.n - 1))) := rfl

/-- The Schur-complement matrix makes the coordinate comparison descend to Picard groups. -/
theorem contractionCoordinates_range (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1))))
    (hw : ∀ i, U.weight (f i) ∣ T.weight (e i.castSucc))
    (ha : ∀ i j, U.intersection (f i) (f j) =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
          T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
            T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1)))) :
    LinearMap.range T.picardMap ≤
      (LinearMap.range U.picardMap).comap (contractionCoordinates T U e f) := sorry

/-- The canonical Picard comparison, obtained by descending the explicit coordinate map. -/
def contractionPicardMap (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1))))
    (hw : ∀ i, U.weight (f i) ∣ T.weight (e i.castSucc))
    (ha : ∀ i j, U.intersection (f i) (f j) =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
          T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
            T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1)))) :
    T.PicardGroup →ₗ[ℤ] U.PicardGroup :=
  Submodule.mapQ (LinearMap.range T.picardMap) (LinearMap.range U.picardMap)
    (contractionCoordinates T U e f) (contractionCoordinates_range T U e f hminus hw ha)

/-- On a represented Picard class the descended map is exactly the coordinate comparison. -/
theorem contractionPicardMap_mk (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1))))
    (hw : ∀ i, U.weight (f i) ∣ T.weight (e i.castSucc))
    (ha : ∀ i j, U.intersection (f i) (f j) =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
          T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
            T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1))))
    (v : Fin T.n → ℤ) :
    contractionPicardMap T U e f hminus hw ha (T.toPicardGroup v) =
      U.toPicardGroup (contractionCoordinates T U e f v) := by
  rw [toPicardGroup_apply, toPicardGroup_apply]
  rfl

/-- Picard comparison remains injective for every dividing choice of retained weights.
No maximality or two-torsion cokernel claim is imposed on the smaller weights. -/
theorem contractionPicardMap_injective (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1))))
    (hw : ∀ i, U.weight (f i) ∣ T.weight (e i.castSucc))
    (ha : ∀ i j, U.intersection (f i) (f j) =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
          T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
            T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1)))) :
    Function.Injective (contractionPicardMap T U e f hminus hw ha) := sorry

end NumericalType
