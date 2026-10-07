module

import Mathlib.AlgebraicGeometry.Limits
import StacksCheckRecall
import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme

universe u

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonObj TensorProduct

section

variable (n : ℕ)

/- Example 39.5.4 (General linear group scheme) (1): the integral general linear group scheme has
the determinant-localized coordinate-ring spectrum as its underlying scheme. -/
@[stacks 022W] #check
  (AlgebraicGeometry.GeneralLinear.groupScheme_left
      (ULift.{u} ℤ) (ULift.{u} (Fin n)) :
    (AlgebraicGeometry.GeneralLinear.groupScheme
      (ULift.{u} ℤ) (ULift.{u} (Fin n))).X.left =
        Spec (CommRingCat.of
          (AlgebraicGeometry.GeneralLinear.coordinateRing
            (ULift.{u} ℤ) (ULift.{u} (Fin n)))))

end

section

variable (n : ℕ)
variable (T : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

/- Example 39.5.4 (General linear group scheme) (2): its points over a scheme over
`Spec (CommRingCat.of (ULift ℤ))` are multiplicatively equivalent to invertible matrices over
global sections. -/
@[stacks 022W] #check
  (AlgebraicGeometry.GeneralLinear.HomOver.mulEquiv
      (ULift.{u} (Fin n)) T :
    (T ⟶ (AlgebraicGeometry.GeneralLinear.groupScheme
      (ULift.{u} ℤ) (ULift.{u} (Fin n))).X) ≃*
        Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤))

end

section

variable (n : ℕ)

/- Example 39.5.4 (General linear group scheme) (3): multiplication on the general linear group
scheme is dual to the comultiplication on the determinant-localized coordinate ring. -/
@[stacks 022W] #check
  (AlgebraicGeometry.GeneralLinear.mul_eq_specMap_comul
      (ULift.{u} ℤ) (ULift.{u} (Fin n)) :
    μ[AlgebraicGeometry.GeneralLinear.schemeOver
      (ULift.{u} ℤ) (ULift.{u} (Fin n))].left =
        AlgebraicGeometry.GeneralLinear.specMapComul
          (ULift.{u} ℤ) (ULift.{u} (Fin n)))

/- Companion coordinate formula for the comultiplication in part (3). -/
#check
  (AlgebraicGeometry.GeneralLinear.CoordinateRing.comul_localizedCoordinate
      (ULift.{u} ℤ) (ULift.{u} (Fin n)) :
    ∀ i j : ULift.{u} (Fin n),
      AlgebraicGeometry.GeneralLinear.CoordinateRing.comul
          (ULift.{u} ℤ) (ULift.{u} (Fin n))
          (AlgebraicGeometry.GeneralLinear.localizedCoordinate
            (ULift.{u} ℤ) (ULift.{u} (Fin n)) i j) =
        ∑ k, Algebra.TensorProduct.includeLeft
              (R := ULift.{u} ℤ)
              (B := AlgebraicGeometry.GeneralLinear.coordinateRing
                (ULift.{u} ℤ) (ULift.{u} (Fin n)))
              (AlgebraicGeometry.GeneralLinear.localizedCoordinate
                (ULift.{u} ℤ) (ULift.{u} (Fin n)) i k) *
            Algebra.TensorProduct.includeRight
              (R := ULift.{u} ℤ)
              (A := AlgebraicGeometry.GeneralLinear.coordinateRing
                (ULift.{u} ℤ) (ULift.{u} (Fin n)))
              (AlgebraicGeometry.GeneralLinear.localizedCoordinate
                (ULift.{u} ℤ) (ULift.{u} (Fin n)) k j))

end

section

variable (S : Scheme.{u}) (n : ℕ)

/- Example 39.5.4 (General linear group scheme) (4): pullback to any scheme `S` remains a group
scheme whose points are invertible matrices over global sections. -/
@[stacks 022W] #check
  (AlgebraicGeometry.GeneralLinear.BaseChange.homMulEquiv
      (AlgebraicGeometry.specULiftZIsTerminal.from S) (ULift.{u} (Fin n)) :
    (T : Over S) →
      (T ⟶ (AlgebraicGeometry.GeneralLinear.baseChange
        (AlgebraicGeometry.specULiftZIsTerminal.from S) (ULift.{u} (Fin n))).X) ≃*
          Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤))

end
