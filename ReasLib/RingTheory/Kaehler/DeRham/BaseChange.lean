module

public import ReasLib.Algebra.Module.DifferentialOperator.DeRham.Equiv
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base Change of de Rham Differential Families

The standard Kähler comparison transports exterior-form differential families
from `Ω[A' ⊗[A] B⁄A']` to `(A' ⊗[A] B) ⊗[B] Ω[B⁄A]`.  The right tensor-product
algebra is selected through its opt-in scope, keeping this owner free of a
second global algebra instance.

@stack 0H8Y
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right
open DifferentialOperator.DeRham

universe u

namespace KaehlerDifferential.DeRham

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

/-- The universal derivation after transport through the Kähler base-change
comparison. -/
@[stacks 0H8Y]
noncomputable def baseChangeDerivation :
    Derivation A' (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Ω[B⁄A]) :=
  (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm.toLinearMap.compDer
    (KaehlerDifferential.D A' (A' ⊗[A] B))

/-- Transport a differential family through the Kähler base-change
comparison. -/
@[stacks 0H8Y]
noncomputable def baseChange
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A']) :
    Family A' (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] Ω[B⁄A]) :=
  Family.transport
    (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ

/-- The Kähler base-change comparison intertwines a differential family with
its transport. -/
@[stacks 0H8Y]
theorem baseChange_descends
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A']) :
    Descends (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).toLinearMap
      (baseChange δ) δ := by
  simpa [baseChange] using
    Family.transport_descends_symm
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ

/-- Base change preserves the square-zero relation of a differential
family. -/
@[stacks 0H8Y]
theorem baseChange_squaresToZero
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : SquaresToZero δ) :
    SquaresToZero (baseChange δ) := by
  simpa [baseChange] using
    Family.transport_squaresToZero
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

/-- Base change transports the de Rham formulas for the universal
derivation. -/
@[stacks 0H8Y]
theorem baseChange_satisfiesFormula
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : SatisfiesFormula (KaehlerDifferential.D A' (A' ⊗[A] B)) δ) :
    SatisfiesFormula baseChangeDerivation (baseChange δ) := by
  simpa [baseChange, baseChangeDerivation] using
    Family.transport_satisfiesFormula
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

/-- The transported family is a de Rham differential family for the
transported derivation. -/
@[stacks 0H8Y]
theorem baseChange_isDifferential
    (δ : Family A' (A' ⊗[A] B) Ω[A' ⊗[A] B⁄A'])
    (hδ : IsDifferential (KaehlerDifferential.D A' (A' ⊗[A] B)) δ) :
    IsDifferential baseChangeDerivation (baseChange δ) := by
  simpa [baseChange, baseChangeDerivation] using
    Family.transport_isDifferential
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).symm δ hδ

end KaehlerDifferential.DeRham
