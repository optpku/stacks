/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.AlgebraicGeometry.NumericalType.Picard
public import ReasLib.LinearAlgebra.Quotient.Map

@[expose] public section

namespace NumericalType

/-- The integral endomorphism presented by the intersection matrix of a numerical type. -/
public def intersectionMap (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T.n → ℤ) :=
  Matrix.toLin' T.intersection

/-- The intersection endomorphism sends the `i`th standard basis vector to the `i`th
column of the symmetric intersection matrix. -/
public theorem intersectionMap_single (T : NumericalType) (i j : Fin T.n) :
    T.intersectionMap (Pi.single i 1) j = T.intersection i j := sorry

/-- The cokernel of the intersection matrix of a numerical type. -/
@[reducible] public def IntersectionCokernel (T : NumericalType) : Type :=
  (Fin T.n → ℤ) ⧸ LinearMap.range T.intersectionMap

/-- The named intersection cokernel is the quotient by the range of `intersectionMap`. -/
public theorem intersectionCokernel_eq_quotient (T : NumericalType) :
    T.IntersectionCokernel =
      ((Fin T.n → ℤ) ⧸ LinearMap.range T.intersectionMap) := sorry

/-- The canonical map from integral coordinate vectors to the intersection cokernel. -/
public def toIntersectionCokernel (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] T.IntersectionCokernel :=
  (LinearMap.range T.intersectionMap).mkQ

/-- The canonical map to the intersection cokernel is the quotient map by the range of
`intersectionMap`. -/
public theorem toIntersectionCokernel_apply (T : NumericalType) (x : Fin T.n → ℤ) :
    T.toIntersectionCokernel x =
      (LinearMap.range T.intersectionMap).mkQ x := sorry

/-- The diagonal endomorphism multiplying each coordinate by its weight. -/
public def weightMap (T : NumericalType) :
    (Fin T.n → ℤ) →ₗ[ℤ] (Fin T.n → ℤ) :=
  Matrix.toLin' (Matrix.diagonal fun i ↦ (T.weight i : ℤ))

/-- The diagonal weight endomorphism multiplies coordinate `i` by `T.weight i`. -/
public theorem weightMap_apply (T : NumericalType) (x : Fin T.n → ℤ) (i : Fin T.n) :
    T.weightMap x i = (T.weight i : ℤ) * x i := sorry

/-- Positivity of the weights makes the diagonal weight endomorphism injective. -/
public theorem weightMap_injective (T : NumericalType) :
    Function.Injective T.weightMap := sorry

/-- Diagonal weight multiplication after the Picard endomorphism is the intersection
endomorphism. -/
public theorem weightMap_comp_picardMap (T : NumericalType) :
    T.weightMap.comp T.picardMap = T.intersectionMap := sorry

/-- The inverse image under diagonal weight multiplication of the intersection range is
exactly the Picard range. -/
public theorem comap_intersectionMap_range (T : NumericalType) :
    (LinearMap.range T.intersectionMap).comap T.weightMap =
      LinearMap.range T.picardMap := sorry

/-- The canonical map from the Picard group to the intersection cokernel induced by
diagonal weight multiplication. -/
public def picardToIntersectionCokernel (T : NumericalType) :
    T.PicardGroup →ₗ[ℤ] T.IntersectionCokernel :=
  (LinearMap.range T.picardMap).mapQ (LinearMap.range T.intersectionMap)
    T.weightMap T.comap_intersectionMap_range.ge

/-- On a canonical representative, `picardToIntersectionCokernel` multiplies every
coordinate by its weight. -/
public theorem picardToIntersectionCokernel_toPicardGroup
    (T : NumericalType) (x : Fin T.n → ℤ) :
    T.picardToIntersectionCokernel (T.toPicardGroup x) =
      T.toIntersectionCokernel (fun i ↦ (T.weight i : ℤ) * x i) := sorry

/-- The canonical map from the Picard group to the intersection cokernel is injective. -/
public theorem picardToIntersectionCokernel_injective (T : NumericalType) :
    Function.Injective T.picardToIntersectionCokernel := sorry

end NumericalType
