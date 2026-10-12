/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RingHom
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct

@[expose] public section

/-!
# Tensor maps through the residue field of a tensor prime

This leaf owns the canonical tensor-product map obtained from a map out of the
residue field at a tensor prime.  Its restriction formulas and kernel
corollaries are independent of strict henselizations and common-field models.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

namespace Localization.AtPrime.TensorProduct.ResidueField

section

variable {A : Type u} {B : Type v} {C : Type w} {K : Type x}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable {pD : Ideal (B ⊗[A] C)} [pD.IsPrime]

section Map

variable [Semiring K]

/-- Tag 0GIP: compose a map from the residue field at a tensor prime with the
canonical map from the tensor product to that residue field. -/
@[stacks 0GIP "tensor-prime residue-field map"]
noncomputable def tensorMap (map : pD.ResidueField →+* K) : B ⊗[A] C →+* K :=
  map.comp (algebraMap (B ⊗[A] C) pD.ResidueField)

section Left

variable {pB : Ideal B} [pB.IsPrime] [pD.LiesOver pB]

/-- The left-factor restriction of a tensor map through `pD.ResidueField` is
the composite through the left residue-field edge. -/
@[simp, stacks 0GIP "tensor-map left restriction"]
theorem restrictLeft_tensorMap (map : pD.ResidueField →+* K) :
    Algebra.TensorProduct.RingHom.restrictLeft (tensorMap map) =
      (map.comp (leftTarget (pB := pB) (pD := pD))).comp
        (algebraMap B pB.ResidueField) := sorry

end Left

section Right

variable {pC : Ideal C} [pC.IsPrime] [pD.LiesOver pC]

/-- The right-factor restriction of a tensor map through `pD.ResidueField` is
the composite through the right residue-field edge. -/
@[simp, stacks 0GIP "tensor-map right restriction"]
theorem restrictRight_tensorMap (map : pD.ResidueField →+* K) :
    Algebra.TensorProduct.RingHom.restrictRight (tensorMap map) =
      (map.comp (rightTarget (pC := pC) (pD := pD))).comp
        (algebraMap C pC.ResidueField) := sorry

end Right

section Base

variable {pA : Ideal A} [pA.IsPrime]
variable {pB : Ideal B} [pB.IsPrime] [pB.LiesOver pA] [pD.LiesOver pB]

/-- The base-ring restriction of a tensor map through `pD.ResidueField` is
the composite through the source-to-target residue-field edge. -/
@[simp, stacks 0GIP "tensor-map base restriction"]
theorem restrictBase_tensorMap (map : pD.ResidueField →+* K) :
    Algebra.TensorProduct.RingHom.restrictBase (tensorMap map) =
      (map.comp (sourceTarget (pA := pA) (pB := pB) (pD := pD))).comp
        (algebraMap A pA.ResidueField) := sorry

end Base

end Map

section Lift

variable [CommRing K]

/-- Composing the canonical tensor-prime residue-field map with Mathlib's
`Ideal.ResidueField.lift` recovers the raw tensor-product map. -/
@[simp, stacks 0GIP "tensor-map residue-field lift"]
theorem tensorMap_lift
    (map : B ⊗[A] C →+* K)
    (hker_le : pD ≤ RingHom.ker map)
    (hunit : pD.primeCompl ≤ (IsUnit.submonoid K).comap map) :
    tensorMap (Ideal.ResidueField.lift pD map hker_le hunit) = map := sorry

end Lift

section FieldLift

variable [Field K]

/-- A raw tensor-product map to a field factors through the residue field of
its kernel, and its resulting tensor map is the original map. -/
@[stacks 0GIP "tensor-map factorization through the kernel residue field"]
theorem tensorMap_lift_of_ker_eq
    (map : B ⊗[A] C →+* K)
    (hker : RingHom.ker map = pD) :
    tensorMap
        (Ideal.ResidueField.lift pD map hker.ge
          (Ideal.primeCompl_le_isUnit_comap_of_ker_eq pD map hker)) = map := sorry

end FieldLift

section Kernel

variable [Semiring K] [Nontrivial K]

/-- The kernel of a tensor map through the residue field at `pD` is exactly
`pD`. -/
@[stacks 0GIP "tensor-map kernel"]
theorem ker_tensorMap (map : pD.ResidueField →+* K) :
    RingHom.ker (tensorMap map) = pD := sorry

section Left

variable {pB : Ideal B} [pB.IsPrime] [pD.LiesOver pB]

/-- The left-factor restriction of a tensor map through `pD` has kernel the
contracted left prime. -/
@[stacks 0GIP "tensor-map left kernel"]
theorem ker_restrictLeft_tensorMap (map : pD.ResidueField →+* K) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictLeft (tensorMap map)) = pB := sorry

end Left

section Right

variable {pC : Ideal C} [pC.IsPrime] [pD.LiesOver pC]

/-- The right-factor restriction of a tensor map through `pD` has kernel the
contracted right prime. -/
@[stacks 0GIP "tensor-map right kernel"]
theorem ker_restrictRight_tensorMap (map : pD.ResidueField →+* K) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictRight (tensorMap map)) = pC := sorry

end Right

section Base

variable {pA : Ideal A} [pA.IsPrime]
variable {pB : Ideal B} [pB.IsPrime] [pB.LiesOver pA] [pD.LiesOver pB]

/-- The base-ring restriction of a tensor map through `pD` has kernel the
source prime. -/
@[stacks 0GIP "tensor-map base kernel"]
theorem ker_restrictBase_tensorMap (map : pD.ResidueField →+* K) :
    RingHom.ker (Algebra.TensorProduct.RingHom.restrictBase (tensorMap map)) = pA := sorry

end Base

end Kernel

end

end Localization.AtPrime.TensorProduct.ResidueField
