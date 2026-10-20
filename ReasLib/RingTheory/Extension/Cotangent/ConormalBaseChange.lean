/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorProduct.BaseRing

/-!
# Conormal cokernels after base change

This file packages the conormal sequence attached to a surjective presentation
`B → A` and a map `A → L`.  The quotient `B / ker(B → A)` is retained as
the scalar owner of `ker(B → A) / ker(B → A) ^ 2`; its canonical equivalence
with `A` keeps the public construction independent of temporary algebra
instances.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open scoped TensorProduct

universe u v w x

namespace AlgHom

/-- A surjective presentation `B → A` of the source of an algebra map
`φ : A →ₐ[R] L`.  The map to `L` is derived as `φ.comp toA`. -/
@[stacks 0BJ5]
structure SurjectivePresentation
    {R : Type u} {A : Type v} {L : Type w}
    [CommRing R] [CommRing A] [CommRing L] [Algebra R A] [Algebra R L]
    (φ : A →ₐ[R] L) where
  /-- The presenting algebra. -/
  B : Type x
  /-- The commutative-ring structure on the presenting algebra. -/
  instCommRingB : CommRing B
  /-- The `R`-algebra structure on the presenting algebra. -/
  instAlgebraRB : Algebra R B
  /-- The surjective presentation map. -/
  toA : B →ₐ[R] A
  /-- The presentation map is surjective. -/
  surjective : Function.Surjective toA

attribute [instance] SurjectivePresentation.instCommRingB
attribute [instance] SurjectivePresentation.instAlgebraRB

namespace SurjectivePresentation

variable {R : Type u} {A : Type v} {L : Type w}
variable [CommRing R] [CommRing A] [CommRing L] [Algebra R A] [Algebra R L]
variable {φ : A →ₐ[R] L} (P : φ.SurjectivePresentation)

/-- Bundle an explicit surjective `R`-algebra map as a surjective presentation. -/
def of {B : Type x} [CommRing B] [Algebra R B]
    (f : B →ₐ[R] A) (hf : Function.Surjective f) : φ.SurjectivePresentation where
  B := B
  instCommRingB := inferInstance
  instAlgebraRB := inferInstance
  toA := f
  surjective := hf

/-- The presentation map of an explicitly bundled surjection is the original
map. -/
@[simp]
theorem toA_of {B : Type x} [CommRing B] [Algebra R B]
    (f : B →ₐ[R] A) {hf : Function.Surjective f} :
    (of (φ := φ) f hf).toA = f := sorry

/-- The composite map from the presenting algebra to the target. -/
def toTarget : P.B →ₐ[R] L :=
  φ.comp P.toA

/-- The target map of an explicitly bundled presentation is the expected
composite. -/
@[simp]
theorem toTarget_of {B : Type x} [CommRing B] [Algebra R B]
    (f : B →ₐ[R] A) {hf : Function.Surjective f} :
    (of (φ := φ) f hf).toTarget = φ.comp f := sorry

/-- The target carries the algebra structure induced by the composite presentation map. -/
noncomputable instance : Algebra P.B L :=
  P.toTarget.toAlgebra

/-- The source, presenting algebra, and target form the scalar tower induced by the composite
map. -/
noncomputable instance : IsScalarTower R P.B L := sorry

/-- The kernel ideal of the surjective presentation. -/
abbrev kernel : Ideal P.B :=
  RingHom.ker P.toA.toRingHom

/-- The quotient of the presenting algebra by the kernel of the presentation. -/
abbrev quotient :=
  P.B ⧸ P.kernel

/-- The first-isomorphism equivalence `B / ker(B → A) ≃ₐ[R] A`. -/
@[stacks 0BJ5]
noncomputable def quotientEquiv : P.quotient ≃ₐ[R] A :=
  Ideal.quotientKerAlgEquivOfSurjective P.surjective

/-- The first-isomorphism equivalence sends the class of a presenting
element to its image in the presented algebra. -/
@[simp]
theorem quotientEquiv_mk (b : P.B) :
    P.quotientEquiv (Ideal.Quotient.mk P.kernel b) = P.toA b := sorry

/-- The first-isomorphism equivalence composed with the quotient map is the
original surjective presentation map. -/
@[simp]
theorem quotientEquiv_comp_mk :
    P.quotientEquiv.toAlgHom.comp (Ideal.Quotient.mkₐ R P.kernel) =
      P.toA := sorry

/-- The presented algebra carries the algebra structure induced by the first-isomorphism
equivalence. -/
noncomputable instance : Algebra P.quotient A :=
  P.quotientEquiv.toAlgHom.toAlgebra

/-- The quotient presentation and target are related by the canonical composite through `A`. -/
noncomputable instance : Algebra P.quotient L :=
  (φ.comp P.quotientEquiv.toAlgHom).toAlgebra

/-- The base and quotient presentation form the expected scalar tower on `A`. -/
noncomputable instance : IsScalarTower R P.quotient A := sorry

/-- The base and quotient presentation form the expected scalar tower on `L`. -/
noncomputable instance : IsScalarTower R P.quotient L := sorry

/-- The closed-center ideal on the presenting algebra, obtained by contracting the maximal ideal
of a local target. -/
def closedCenter [IsLocalRing L] : Ideal P.B :=
  Ideal.comap P.toTarget.toRingHom (maximalIdeal L)

/-- The closed center of a surjective presentation over a local target is prime. -/
instance closedCenter_isPrime [IsLocalRing L] : P.closedCenter.IsPrime := sorry

/-- The prime-spectrum point corresponding to the closed center of the presentation. -/
abbrev closedCenterPoint [IsLocalRing L] : PrimeSpectrum P.B :=
  ⟨P.closedCenter, inferInstance⟩

/-- The target module `L ⊗[ B ] Ω[B/R]` of the base-changed conormal map. -/
abbrev ConormalTarget :=
  L ⊗[P.B] Ω[P.B⁄R]

/-- The kernel of the presentation is contained in the kernel of its composite map to the
target. -/
theorem kernel_le_targetKernel :
    P.kernel ≤ RingHom.ker (algebraMap P.B L) := sorry

/-- The differential of an element of the presentation kernel, viewed in
`L ⊗[ B ] Ω[B/R]`. -/
noncomputable def kernelToTarget : P.kernel →ₗ[P.B] P.ConormalTarget :=
  (KaehlerDifferential.kerToTensor R P.B L).comp
    (Submodule.inclusion P.kernel_le_targetKernel)

/-- Products of two elements of the presentation kernel vanish under the base-changed
differential map. -/
theorem kernelToTarget_mul_eq_zero (a b : P.kernel) :
    P.kernelToTarget (a * b) = 0 := sorry

/-- The underlying `B`-linear conormal map
`ker(B → A) / ker(B → A) ^ 2 → L ⊗[ B ] Ω[B/R]`. -/
noncomputable def cotangentToTargetUnderlying :
    P.kernel.Cotangent →ₗ[P.B] P.ConormalTarget :=
  Ideal.Cotangent.lift P.kernelToTarget P.kernelToTarget_mul_eq_zero

/-- The underlying conormal map respects the canonical `B / ker(B → A)`-module
structures. -/
theorem cotangentToTargetUnderlying_map_smul
    (r : P.quotient) (x : P.kernel.Cotangent) :
    P.cotangentToTargetUnderlying (r • x) =
      r • P.cotangentToTargetUnderlying x := sorry

/-- The canonical conormal map, linear over the quotient presentation. -/
@[stacks 0BJ5]
noncomputable def cotangentToTarget :
    P.kernel.Cotangent →ₗ[P.quotient] P.ConormalTarget where
  toFun := P.cotangentToTargetUnderlying
  map_add' := P.cotangentToTargetUnderlying.map_add
  map_smul' := P.cotangentToTargetUnderlying_map_smul

/-- The source `(L ⊗[ B / ker(B → A) ] ker(B → A) / ker(B → A) ^ 2)` of the
base-changed conormal map. -/
abbrev ConormalSource :=
  L ⊗[P.quotient] P.kernel.Cotangent

/-- Scalar multiplication contracts `L ⊗[ B / ker(B → A) ] (L ⊗[ B ] Ω[B/R])`
to `L ⊗[ B ] Ω[B/R]`. -/
noncomputable def targetTensorAction :
    L ⊗[P.quotient] P.ConormalTarget →ₗ[L] P.ConormalTarget :=
  TensorProduct.AlgebraTensorModule.lift <|
    LinearMap.restrictScalarsₗ P.quotient L P.ConormalTarget P.ConormalTarget L ∘ₗ
      LinearMap.lsmul L P.ConormalTarget

/-- The conormal map after extending scalars to the target algebra. -/
@[stacks 0BJ5]
noncomputable def conormalBaseChangeMap :
    P.ConormalSource →ₗ[L] P.ConormalTarget :=
  P.targetTensorAction.comp (P.cotangentToTarget.baseChange L)

/-- The cokernel of the conormal map after extending scalars to the target algebra. -/
@[stacks 0BJ5]
abbrev ConormalCokernel :=
  P.ConormalTarget ⧸ LinearMap.range P.conormalBaseChangeMap

/-- The base change of the Kähler differentials of the presented algebra, expressed over the
canonical quotient presentation. -/
abbrev KaehlerBaseChange :=
  L ⊗[P.quotient] Ω[A⁄R]

/-- Freeness of the base-changed conormal cokernel is equivalent to freeness of the corresponding
base change of `Ω[A/R]`. -/
@[stacks 0BJ5 "conormal cokernel and quotient-base Kahler module"]
theorem conormalCokernel_free_iff_quotient :
    Module.Free L P.ConormalCokernel ↔ Module.Free L P.KaehlerBaseChange := sorry

/-- The quotient presentation and the ambient source algebra act identically on the target when
the presentation map agrees with the ambient algebra map. -/
theorem quotient_smul_target
    [Algebra A L] (hφ : φ.toRingHom = algebraMap A L)
    (q : P.quotient) (l : L) :
    q • l = P.quotientEquiv q • l := sorry

/-- The quotient presentation acts on Kahler differentials through its canonical equivalence with
the presented source algebra. -/
theorem quotient_smul_kaehler (q : P.quotient) (x : Ω[A⁄R]) :
    q • x = P.quotientEquiv q • x := sorry

/-- The quotient-based model of the base-changed Kahler module is canonically equivalent to the
usual base change along `A → L`. -/
@[stacks 0BJ5 "quotient and source base changes of Kahler differentials"]
noncomputable def kaehlerBaseChangeEquiv
    [Algebra A L] (hφ : φ.toRingHom = algebraMap A L) :
    P.KaehlerBaseChange ≃ₗ[L] L ⊗[A] Ω[A⁄R] :=
  TensorProduct.baseRingEquiv P.quotientEquiv.toRingEquiv
    (P.quotient_smul_target hφ) P.quotient_smul_kaehler

/-- The canonical comparison between the two base-change models fixes pure tensors. -/
@[stacks 0BJ5 "Kahler base-change comparison on pure tensors", simp]
theorem kaehlerBaseChangeEquiv_tmul
    [Algebra A L] (hφ : φ.toRingHom = algebraMap A L)
    (l : L) (x : Ω[A⁄R]) :
    P.kaehlerBaseChangeEquiv hφ (l ⊗ₜ x) = l ⊗ₜ x := sorry

/-- Freeness of the conormal cokernel is equivalent to freeness of the standard base change
`L ⊗[ A ] Ω[A/R]`. -/
@[stacks 0BJ5]
theorem conormalCokernel_free_iff
    [Algebra A L] (hφ : φ.toRingHom = algebraMap A L) :
    Module.Free L P.ConormalCokernel ↔ Module.Free L (L ⊗[A] Ω[A⁄R]) := sorry

end SurjectivePresentation

end AlgHom
