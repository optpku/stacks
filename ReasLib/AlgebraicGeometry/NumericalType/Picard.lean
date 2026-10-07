module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.AlgebraicGeometry.NumericalType

open scoped BigOperators

namespace NumericalType

/-- The integral matrix whose `(i, j)` entry is the intersection number divided by
the weight of index `i`. -/
public def picardMatrix (T : NumericalType) : Matrix (Fin T.n) (Fin T.n) ℤ :=
  fun i j ↦ T.intersection i j / (T.weight i : ℤ)

/-- An entry of `picardMatrix` is the corresponding intersection number divided by its
row weight. -/
public theorem picardMatrix_apply (T : NumericalType) (i j : Fin T.n) :
    T.picardMatrix i j = T.intersection i j / (T.weight i : ℤ) := sorry

/-- Multiplication by the row weight recovers the corresponding intersection entry. -/
public theorem weight_mul_picardMatrix (T : NumericalType) (i j : Fin T.n) :
    (T.weight i : ℤ) * T.picardMatrix i j = T.intersection i j := sorry

/-- The integral endomorphism presented by `picardMatrix`. -/
public def picardMap (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T.n → ℤ) :=
  Matrix.toLin' T.picardMatrix

/-- The coordinate formula for the Picard endomorphism. -/
public theorem picardMap_apply (T : NumericalType) (x : Fin T.n → ℤ) (j : Fin T.n) :
    T.picardMap x j =
      ∑ i, (T.intersection j i / (T.weight j : ℤ)) * x i := sorry

/-- The Picard endomorphism sends the `i`th standard basis vector to the vector whose
`j`th coordinate is the intersection number divided by the weight of `j`. -/
public theorem picardMap_single (T : NumericalType) (i j : Fin T.n) :
    T.picardMap (Pi.single i 1) j =
      T.intersection i j / (T.weight j : ℤ) := sorry

/-- The Picard group of a numerical type, presented as the quotient by the range of its
Picard endomorphism. -/
public abbrev PicardGroup (T : NumericalType) : Type :=
  (Fin T.n → ℤ) ⧸ LinearMap.range T.picardMap

/-- The named Picard group is the quotient by the range of the Picard endomorphism. -/
public theorem picardGroup_eq_quotient (T : NumericalType) :
    T.PicardGroup = ((Fin T.n → ℤ) ⧸ LinearMap.range T.picardMap) := sorry

/-- The canonical map from integral coordinate vectors to the Picard group. -/
public def toPicardGroup (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] T.PicardGroup :=
  (LinearMap.range T.picardMap).mkQ

/-- The canonical map to the Picard group is the quotient map by the range of
`picardMap`. -/
public theorem toPicardGroup_apply (T : NumericalType) (x : Fin T.n → ℤ) :
    T.toPicardGroup x = (LinearMap.range T.picardMap).mkQ x := sorry

/-- The canonical map to the Picard group annihilates the Picard endomorphism. -/
public theorem picardMap_toPicardGroup (T : NumericalType) :
    T.toPicardGroup.comp T.picardMap = 0 := sorry

/-- The Picard endomorphism followed by the quotient map is exact. -/
public theorem picardGroup_exact (T : NumericalType) :
    Function.Exact T.picardMap T.toPicardGroup := sorry

/-- Every Picard-group class is represented by an integral coordinate vector. -/
public theorem toPicardGroup_surjective (T : NumericalType) :
    Function.Surjective T.toPicardGroup := sorry

/-- The integral Picard group of every numerical type has finrank one. -/
public theorem picardGroup_finrank (T : NumericalType) :
    Module.finrank ℤ T.PicardGroup = 1 := sorry

end NumericalType
