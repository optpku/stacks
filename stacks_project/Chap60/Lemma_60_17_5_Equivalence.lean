/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.NatIso
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import stacks_project.Chap60.Proposition_60_17_4_Categories
public import stacks_project.Chap60.Proposition_60_17_4_Functor
public import stacks_project.Chap60.Remark_60_6_9_BaseChange
public import stacks_project.Chap60.Lemma_60_17_5_Retract

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair
open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')
variable [Algebra.Smooth A P']
variable (R : DividedPowerRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

namespace CrystallineConnectionPair

/-- The `p`-adic ideal of the completed envelope `D'`. -/
noncomputable def crystallineDOf.pIdeal :
    Ideal R.smoothD :=
  Ideal.span {(p : R.smoothD)}

/-- Unfolding of the `p`-adic ideal of `D'`. -/
theorem crystallineDOf.pIdeal_eq :
    crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R =
      Ideal.span {(p : R.smoothD)} :=
  sorry

/-- The completed tensor `M ⊗^∧_{D'} Ω_{D'}` appearing as the codomain of `∇'`. -/
noncomputable def completedTensorOf
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] : Type u :=
  AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
    (M ⊗[R.smoothD] R.omegaSmooth)

/-- Unfolding of the completed tensor over `D'`. -/
theorem completedTensorOf_eq
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M =
      AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
        (M ⊗[R.smoothD] R.omegaSmooth) :=
  sorry

/-- Additive group structure on the completed tensor over `D'`. -/
noncomputable instance completedTensorOf.addCommGroup
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    AddCommGroup (completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  inferInstanceAs (AddCommGroup
    (AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (M ⊗[R.smoothD] R.omegaSmooth)))

/-- `D'`-module structure on the completed tensor over `D'`. -/
noncomputable instance completedTensorOf.module
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    Module R.smoothD
      (completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  inferInstanceAs (Module R.smoothD
    (AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (M ⊗[R.smoothD] R.omegaSmooth)))

/-- Canonical map from the uncompleted tensor into the completed tensor over `D'`. -/
noncomputable def completedTensorOf.of
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    M ⊗[R.smoothD] R.omegaSmooth →+
      completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M :=
  AddMonoidHom.mk'
    (fun ω =>
      AdicCompletion.of (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
        (M ⊗[R.smoothD] R.omegaSmooth) ω)
    sorry

/-- Functoriality of completed tensors over `D'` in the module variable. -/
noncomputable def completedTensorOf.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.smoothD M] [Module R.smoothD N]
    (f : M →ₗ[R.smoothD] N) :
    completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+
      completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N :=
  (AdicCompletion.map (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
    (TensorProduct.map f (LinearMap.id (R := R.smoothD) (M := R.omegaSmooth)))).toAddMonoidHom

/-- `A`-algebra structure on `D'` along the retract map `a : D → D'`. -/
@[reducible] noncomputable def algebraAlongA : Algebra R.polyD R.smoothD :=
  R.a.toAlgebra

/-- `A`-algebra structure on `D` along the retract map `b : D' → D`. -/
@[reducible] noncomputable def algebraAlongB : Algebra R.smoothD R.polyD :=
  R.b.toAlgebra

/-- The Remark 60.6.9 comparison `φ : Ω_D → Ω_{D'}` as a `D`-linear map, via
restriction of scalars along `a`. -/
noncomputable def formsALinear :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.polyD R.smoothD :=
      algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    R.omegaPoly →ₗ[R.polyD] R.omegaSmooth :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun := fun ω => (R.formsA) ω
    map_add' := fun x y => (R.formsA).map_add x y
    map_smul' := fun r ω =>
      DividedPowerRetract.formsA_smul p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R r ω }

/-- The Remark 60.6.9 comparison `Ω_{D'} → Ω_D` as a `D'`-linear map, via
restriction of scalars along `b`. -/
noncomputable def formsBLinear :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.smoothD R.polyD :=
      algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    R.omegaSmooth →ₗ[R.smoothD] R.omegaPoly :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun := fun ω => (R.formsB) ω
    map_add' := fun x y => (R.formsB).map_add x y
    map_smul' := fun r ω =>
      DividedPowerRetract.formsB_smul p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R r ω }

/-- `formsALinear` is the additive map `formsA`. -/
theorem formsALinear_apply (ω : R.omegaPoly) :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.polyD R.smoothD :=
      algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    formsALinear p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ω = (R.formsA) ω :=
  sorry

/-- `formsBLinear` is the additive map `formsB`. -/
theorem formsBLinear_apply (ω : R.omegaSmooth) :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.smoothD R.polyD :=
      algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    formsBLinear p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ω = (R.formsB) ω :=
  sorry

/-- Scalar extension `M ⊗[D, a] D'` along the retract map `a`. -/
@[reducible] noncomputable def baseChangeTensorA
    (M : Type u) [AddCommGroup M] [Module R.polyD M] : Type u :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  M ⊗[R.polyD] R.smoothD

/-- `D'`-module structure on `M ⊗[D, a] D'`, transported across tensor symmetry. -/
noncomputable instance baseChangeTensorA.moduleSmooth
    (M : Type u) [AddCommGroup M] [Module R.polyD M] :
    Module R.smoothD (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  (TensorProduct.comm R.polyD M R.smoothD).toAddEquiv.module R.smoothD

/-- Scalar extension `M' ⊗[D', b] D` along the retract map `b`. -/
@[reducible] noncomputable def baseChangeTensorB
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] : Type u :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  M ⊗[R.smoothD] R.polyD

/-- `D`-module structure on `M' ⊗[D', b] D`. -/
noncomputable instance baseChangeTensorB.modulePoly
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    Module R.polyD (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  (TensorProduct.comm R.smoothD M R.polyD).toAddEquiv.module R.polyD

/-- Underlying module of `F(M, ∇) = M ⊗^∧_{D, a} D'`. -/
@[reducible] noncomputable def baseChangeCarrierA
    (M : Type u) [AddCommGroup M] [Module R.polyD M] : Type u :=
  AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
    (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)

/-- Additive group of the completed scalar extension along `a`. -/
noncomputable instance baseChangeCarrierA.addCommGroup
    (M : Type u) [AddCommGroup M] [Module R.polyD M] :
    AddCommGroup (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  inferInstanceAs (AddCommGroup
    (AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)))

/-- `D'`-module structure on the completed scalar extension along `a`. -/
noncomputable instance baseChangeCarrierA.moduleSmooth
    (M : Type u) [AddCommGroup M] [Module R.polyD M] :
    Module R.smoothD (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  inferInstanceAs (Module R.smoothD
    (AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)))

/-- Underlying module of `G(M', ∇') = M' ⊗^∧_{D', b} D`. -/
@[reducible] noncomputable def baseChangeCarrierB
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] : Type u :=
  AdicCompletion (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)

/-- Additive group of the completed scalar extension along `b`. -/
noncomputable instance baseChangeCarrierB.addCommGroup
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    AddCommGroup (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  inferInstanceAs (AddCommGroup
    (AdicCompletion (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)))

/-- `D`-module structure on the completed scalar extension along `b`. -/
noncomputable instance baseChangeCarrierB.modulePoly
    (M : Type u) [AddCommGroup M] [Module R.smoothD M] :
    Module R.polyD (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  inferInstanceAs (Module R.polyD
    (AdicCompletion (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)))

/-- `D'`-linear map `f ⊗ id` on `M ⊗[D, a] D'`. -/
noncomputable def baseChangeTensorA.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.polyD M] [Module R.polyD N]
    (f : M →ₗ[R.polyD] N) :
    baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.smoothD]
      baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun := TensorProduct.map f (LinearMap.id (R := R.polyD) (M := R.smoothD))
    map_add' := sorry
    map_smul' := sorry }

/-- Completed scalar extension of a `D`-linear map along `a`. -/
noncomputable def baseChangeCarrierA.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.polyD M] [Module R.polyD N]
    (f : M →ₗ[R.polyD] N) :
    baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.smoothD]
      baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun :=
      AdicCompletion.map (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
        (baseChangeTensorA.map p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f)
    map_add' := sorry
    map_smul' := sorry }

/-- `D`-linear map `g ⊗ id` on `M' ⊗[D', b] D`. -/
noncomputable def baseChangeTensorB.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.smoothD M] [Module R.smoothD N]
    (f : M →ₗ[R.smoothD] N) :
    baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.polyD]
      baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun := TensorProduct.map f (LinearMap.id (R := R.smoothD) (M := R.polyD))
    map_add' := sorry
    map_smul' := sorry }

/-- Completed scalar extension of a `D'`-linear map along `b`. -/
noncomputable def baseChangeCarrierB.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.smoothD M] [Module R.smoothD N]
    (f : M →ₗ[R.smoothD] N) :
    baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.polyD]
      baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  { toFun :=
      AdicCompletion.map
        (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (baseChangeTensorB.map p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f)
    map_add' := sorry
    map_smul' := sorry }

/-- Uncompleted connection `M → M ⊗_D Ω_D` recovered from the coordinate operators of `∇`. -/
noncomputable def uncompletedNablaAlongA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M) :
    M →+ M ⊗[R.polyD] R.omegaPoly :=
  -- Local instance justification (proof-local temporary data):
  -- `polynomialIndex n` is a finite universe-lifted `Fin`.
  letI : Fintype (polynomialIndex R.n) := inferInstance
  AddMonoidHom.mk'
    (fun m =>
      (Finset.univ : Finset (polynomialIndex R.n)).sum fun i =>
        connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
            M hComplete nabla i m ⊗ₜ[R.polyD]
          crystallineOmegaD.dX p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar i)
    sorry

/-- Polynomial-side uncompleted connection recovered from the `dX_i` basis of `Ω_D`. -/
noncomputable def connectionUncompletedAlongA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M) :
    Connection
      (crystallineOmegaD_derivation
        (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p) M :=
  Connection.of
    (uncompletedNablaAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla)
    sorry

/-- Uncompleted Remark 60.6.9 base change of `∇` along `a`, before `p`-adic completion. -/
noncomputable def baseChangeUncompletedAlongA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M) :
    baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+
      baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.smoothD] R.omegaSmooth :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- `Connection.baseChange` needs `A`-modules of forms and restriction of scalars along `a`.
  letI : Module A R.omegaPoly := Module.compHom R.omegaPoly (algebraMap A R.polyD)
  letI : Module A R.omegaSmooth := Module.compHom R.omegaSmooth (algebraMap A R.smoothD)
  letI : IsScalarTower A R.polyD R.omegaPoly := sorry
  letI : IsScalarTower A R.smoothD R.omegaSmooth := sorry
  letI : Module R.polyD R.omegaSmooth := Module.compHom R.omegaSmooth R.a
  letI : IsScalarTower R.polyD R.smoothD R.omegaSmooth := sorry
  (Connection.baseChange
      (connectionUncompletedAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla)
      (formsALinear p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      sorry :
      Connection
        (crystallineOmegaD_derivation
          (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p)
        (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)).toAddMonoidHom

/-- Completed Remark 60.6.9 base change of a connection along `a : D → D'`. -/
noncomputable def baseChangeNablaAlongA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M) :
    baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+
      completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
        (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  let uncomp :=
    baseChangeUncompletedAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla
  let ofMod :=
    AdicCompletion.of (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
  let lin :
      baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.smoothD]
        (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.smoothD]
          R.omegaSmooth) :=
    { toFun := fun t =>
        TensorProduct.map ofMod
            (LinearMap.id (R := R.smoothD) (M := R.omegaSmooth))
          (uncomp t)
      map_add' := sorry
      map_smul' := sorry }
  (AdicCompletion.map (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
    lin).toAddMonoidHom

/-- On pure tensors, `baseChangeNablaAlongA` is the completed Remark 60.6.9 formula
`∇'(m ⊗ d') = ∑ mᵢ ⊗ d' φ(ωᵢ) + m ⊗ d d'` when `∇(m) = ∑ mᵢ ⊗ ωᵢ`. -/
theorem baseChangeNablaAlongA_spec
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M)
    (m : M) (d' : R.smoothD) :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.polyD R.smoothD :=
      algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    baseChangeNablaAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla
        (AdicCompletion.of (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
          (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
          (m ⊗ₜ[R.polyD] d')) =
      completedTensorOf.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R _
        ((TensorProduct.liftAddHom
            (M := M) (N := R.omegaPoly)
            (P :=
              baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.smoothD]
                R.omegaSmooth)
            (R := R.polyD)
            { toFun := fun mi =>
                { toFun := fun ω =>
                    (AdicCompletion.of
                        (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
                        (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
                        (mi ⊗ₜ[R.polyD] d')) ⊗ₜ[R.smoothD]
                      formsALinear p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ω
                  map_zero' := sorry
                  map_add' := sorry }
              map_zero' := sorry
              map_add' := sorry }
            sorry
            (uncompletedNablaAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete
              nabla m) :
          baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.smoothD]
            R.omegaSmooth) +
          ((AdicCompletion.of
                (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
                (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
                (m ⊗ₜ[R.polyD] (1 : R.smoothD))) ⊗ₜ[R.smoothD]
            (crystallineOmegaD_derivation
              (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p d') :
            baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.smoothD]
              R.omegaSmooth)) :=
  sorry

/-- Coefficient of `d x_i` on `M' ⊗_{D'} Ω_{D'}` after applying `formsB`. -/
noncomputable def uncompletedCoordAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M] (i : polynomialIndex R.n) :
    M ⊗[R.smoothD] R.omegaSmooth →ₗ[R.smoothD] M :=
  { toFun := fun t =>
      TensorProduct.liftAddHom
        (M := M) (N := R.omegaSmooth) (P := M) (R := R.smoothD)
        { toFun := fun m =>
            { toFun := fun ω =>
                R.a (crystallineOmegaD.coord p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
                    R.γbar i ((R.formsB) ω)) • m
              map_zero' := sorry
              map_add' := sorry }
          map_zero' := sorry
          map_add' := sorry }
        sorry t
    map_add' := sorry
    map_smul' := sorry }

/-- Completed coordinate of a pair over `D'` along the polynomial basis of `Ω_D`. -/
noncomputable def completedCoordAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M] (i : polynomialIndex R.n) :
    completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.smoothD]
      AdicCompletion (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M :=
  { toFun :=
      AdicCompletion.map (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
        (uncompletedCoordAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R i)
    map_add' := sorry
    map_smul' := sorry }

/-- Coordinate operators of a pair over `D'`, obtained by transporting `∇'` along `formsB`. -/
noncomputable def partialAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (i : polynomialIndex R.n) : M →+ M :=
  -- Local instance justification (proof-local temporary data):
  -- `ofLinearEquiv` needs completeness of the `D'`-module.
  letI := hComplete
  (AdicCompletion.ofLinearEquiv
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M).symm.toAddMonoidHom.comp
    ((completedCoordAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R i).toAddMonoidHom.comp nabla)

/-- Identify `p`-adic completions of a module after changing the scalar ring
along a map that preserves `p`. -/
noncomputable def adicCompletionChangePIdeal
    {D D' : Type u} [CommRing D] [CommRing D']
    {M : Type u} [AddCommGroup M] [Module D M] [Module D' M]
    (JD : Ideal D) (JD' : Ideal D') :
    AdicCompletion JD' M →+ AdicCompletion JD M :=
  AddMonoidHom.mk'
    (fun x =>
      ⟨fun n =>
        (AdicCompletion.of JD M (Quotient.out (x.val n))).val n
      , sorry⟩)
    sorry

/-- Remark 60.6.9 pairing `M ⊗ Ω_{D'} → (M ⊗_b D) ⊗ Ω_D` along `formsB` and a scalar `d`. -/
noncomputable def pairingTensorAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (d : R.polyD) :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.smoothD R.polyD :=
      algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    -- Local instance justification (proof-local temporary data):
    -- restriction of scalars along `b` is needed to state `D'`-linearity of the pairing.
    letI : Module R.smoothD
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
          R.omegaPoly) :=
      Module.compHom
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
          R.omegaPoly) R.b
    M ⊗[R.smoothD] R.omegaSmooth →ₗ[R.smoothD]
      baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD] R.omegaPoly :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- restriction of scalars along `b` makes the polynomial tensor a `D'`-module.
  letI : Module R.smoothD
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
    Module.compHom
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) R.b
  letI : Module R.smoothD R.omegaPoly := Module.compHom R.omegaPoly R.b
  letI : Module R.smoothD
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
        R.omegaPoly) :=
    Module.compHom
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
        R.omegaPoly) R.b
  let ofMod :=
    AdicCompletion.of (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
  { toFun := fun t =>
      TensorProduct.liftAddHom
        (M := M) (N := R.omegaSmooth)
        (P :=
          baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
            R.omegaPoly)
        (R := R.smoothD)
        { toFun := fun mi =>
            { toFun := fun ω =>
                (ofMod (mi ⊗ₜ[R.smoothD] d)) ⊗ₜ[R.polyD]
                  formsBLinear p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ω
              map_zero' := sorry
              map_add' := sorry }
          map_zero' := sorry
          map_add' := sorry }
        sorry t
    map_add' := sorry
    map_smul' := sorry }

/-- Completed Remark 60.6.9 value of `G(∇')` on a pure tensor `m ⊗ d`, using the
actual completed connection `∇'` (not a polynomial-coordinate reconstruction). -/
noncomputable def baseChangeNablaAlongB_tmul
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (m : M) (d : R.polyD) :
    CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
      R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- restriction of scalars along `b` makes the polynomial tensor a `D'`-module.
  letI : Module R.smoothD
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
        R.omegaPoly) :=
    Module.compHom
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M ⊗[R.polyD]
        R.omegaPoly) R.b
  let ofMod :=
    AdicCompletion.of (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
  let resultType :=
    CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
      R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
  let lhs : resultType :=
    adicCompletionChangePIdeal
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
      (AdicCompletion.map
        (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
        (pairingTensorAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R d)
        (nabla m))
  let rhs : resultType :=
    CrystallineConnectionPair.completedTensor.of p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
      R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
      ((ofMod (m ⊗ₜ[R.smoothD] (1 : R.polyD))) ⊗ₜ[R.polyD]
        (crystallineOmegaD_derivation
          (crystallineDBaseMap p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) R.γbar p d))
  lhs + rhs

/-- Uncompleted Remark 60.6.9 base change of the actual `∇'` along `b`. -/
noncomputable def baseChangeUncompletedAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :
    baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+
      CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
        R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  TensorProduct.liftAddHom
    (M := M) (N := R.polyD)
    (P :=
      CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
        R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M))
    (R := R.smoothD)
    { toFun := fun m =>
        { toFun := fun d =>
            baseChangeNablaAlongB_tmul p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nabla m d
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- Completed Remark 60.6.9 base change of a connection along `b : D' → D`. -/
noncomputable def baseChangeNablaAlongB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :
    baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+
      CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
        R.γbar (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :=
  let uncomp :=
    baseChangeUncompletedAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla
  AddMonoidHom.mk'
    (fun y =>
      ⟨fun n =>
        (uncomp (Quotient.out (y.val n))).val n
      , sorry⟩)
    sorry

/-- On pure tensors, `baseChangeNablaAlongB` is the completed Remark 60.6.9
base change of the actual `∇'` along `b`. -/
theorem baseChangeNablaAlongB_spec
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (m : M) (d : R.polyD) :
    -- Local instance justification (noncanonical choice): competing Algebra along a vs b
    letI : Algebra R.smoothD R.polyD :=
      algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete nabla
        (AdicCompletion.of (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
          (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
          (m ⊗ₜ[R.smoothD] d)) =
      baseChangeNablaAlongB_tmul p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nabla m d :=
  sorry

/-- Integrability (07JD) of a pair over `D'`, as integrability of its base change along `b`. -/
def integrableAlongB
    (M : Type u) [AddCommGroup M] [Module R.smoothD M]
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (hM : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)) : Prop :=
  ∀ i j : polynomialIndex R.n,
    (connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) hComplete
        (baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nabla) i).comp
      (connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) hComplete
        (baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nabla) j) =
    (connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) hComplete
        (baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nabla) j).comp
      (connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) hComplete
        (baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nabla) i)

/-- Topological quasi-nilpotence (07JE) of a pair over `D'`, transported along `b`. -/
def quasiNilpotentAlongB
    (M : Type u) [AddCommGroup M] [Module R.smoothD M]
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (hM : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)) : Prop :=
  ∀ (m : baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) (i : polynomialIndex R.n),
    Set.Finite
      {k : ℕ |
        (connectionPartialOf p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
            (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) hComplete
            (baseChangeNablaAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nabla) i)^[k] m ∉
          (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE •
            (⊤ : Submodule R.polyD
              (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)))}

/-- Bundled pairs `(M', ∇')` over the smooth completed envelope `D'`.
Integrability and topological quasi-nilpotence are the corresponding properties of the
base change along `b`. -/
structure ConnectionPairOverSmooth where
  /-- The underlying `D'`-module. -/
  M : Type u
  /-- Additive group structure on `M`. -/
  addCommGroup : AddCommGroup M
  /-- `D'`-module structure on `M`. -/
  module : Module R.smoothD M
  /-- `p`-adic completeness of `M` (07JB). -/
  isAdicComplete : IsAdicComplete
    (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M
  /-- The additive connection map into the completed tensor over `D'`. -/
  nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M
  /-- The Leibniz identity for `∇'` against `d : D' → Ω_{D'}` (07JC). -/
  leibniz :
    ∀ (b : R.smoothD) (m : M),
      nabla (b • m) =
        b • nabla m +
          completedTensorOf.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M
            (m ⊗ₜ[R.smoothD]
              crystallineOmegaD_derivation
                (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p b)
  /-- Completeness of the base change of `M` along `b`, as required to state (07JD) and (07JE). -/
  baseChangeComplete : IsAdicComplete
    (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
    (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
  /-- Integrability (07JD), defined as integrability of the base change along `b`. -/
  isIntegrable : integrableAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M nabla
    isAdicComplete baseChangeComplete
  /-- Topological quasi-nilpotence (07JE), defined by transport along `b`. -/
  isTopologicallyQuasiNilpotent : quasiNilpotentAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
    M nabla isAdicComplete baseChangeComplete

/-- Bundle a completed connection over `D'` from its connection map and the transported laws. -/
noncomputable def ConnectionPairOverSmooth.of
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (leibniz : ∀ (b : R.smoothD) (m : M),
      nabla (b • m) =
        b • nabla m +
          completedTensorOf.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M
            (m ⊗ₜ[R.smoothD]
              crystallineOmegaD_derivation
                (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p b))
    (baseChangeComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M))
    (isIntegrable : integrableAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M nabla
      hComplete baseChangeComplete)
    (isTopologicallyQuasiNilpotent : quasiNilpotentAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
      M nabla hComplete baseChangeComplete) :
    ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R :=
  { M := M
    addCommGroup := inferInstance
    module := inferInstance
    isAdicComplete := hComplete
    nabla := nabla
    leibniz := leibniz
    baseChangeComplete := baseChangeComplete
    isIntegrable := isIntegrable
    isTopologicallyQuasiNilpotent := isTopologicallyQuasiNilpotent }

/-- The smart constructor retains the supplied connection map and the laws (07JB)–(07JE). -/
theorem ConnectionPairOverSmooth.of_spec
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M)
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (leibniz : ∀ (b : R.smoothD) (m : M),
      nabla (b • m) =
        b • nabla m +
          completedTensorOf.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M
            (m ⊗ₜ[R.smoothD]
              crystallineOmegaD_derivation
                (crystallineDOfBaseMap p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE') R.γbar' p b))
    (baseChangeComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
      (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M))
    (isIntegrable : integrableAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M nabla
      hComplete baseChangeComplete)
    (isTopologicallyQuasiNilpotent : quasiNilpotentAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
      M nabla hComplete baseChangeComplete) :
    let Q := ConnectionPairOverSmooth.of p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete
      nabla leibniz baseChangeComplete isIntegrable isTopologicallyQuasiNilpotent
    Q.isAdicComplete = hComplete ∧ Q.nabla = nabla ∧
      Q.leibniz = leibniz ∧ Q.isIntegrable = isIntegrable ∧
      Q.isTopologicallyQuasiNilpotent = isTopologicallyQuasiNilpotent :=
  sorry

/-- Morphisms of completed connection pairs over `D'`. -/
structure ConnectionPairOverSmooth.Hom
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.smoothD M] [Module R.smoothD N]
    (nablaM : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
    (nablaN : N →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N) where
  /-- The underlying `D'`-linear map. -/
  toLinearMap : M →ₗ[R.smoothD] N
  /-- Commutation with the completed connections. -/
  commutes (m : M) :
    nablaN (toLinearMap m) =
      completedTensorOf.map p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R toLinearMap (nablaM m)

/-- Identity morphism of a pair over `D'`. -/
noncomputable def ConnectionPairOverSmooth.Hom.id
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (nabla : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) :
    ConnectionPairOverSmooth.Hom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nabla nabla :=
  { toLinearMap := LinearMap.id
    commutes := sorry }

/-- Composition of morphisms of pairs over `D'`. -/
noncomputable def ConnectionPairOverSmooth.Hom.comp
    {M N Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module R.smoothD M] [Module R.smoothD N] [Module R.smoothD Q]
    {nablaM : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M}
    {nablaN : N →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N}
    {nablaQ : Q →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q}
    (f : ConnectionPairOverSmooth.Hom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nablaM nablaN)
    (g : ConnectionPairOverSmooth.Hom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nablaN nablaQ) :
    ConnectionPairOverSmooth.Hom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R nablaM nablaQ :=
  { toLinearMap := g.toLinearMap.comp f.toLinearMap
    commutes := sorry }

/-- Completed base change of a `D`-linear map along `a`, as a morphism of pairs over `D'`. -/
noncomputable def mapHomAlongA
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.polyD M] [Module R.polyD N]
    (nablaM :
      M →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar M)
    (nablaN :
      N →+
        CrystallineConnectionPair.completedTensor p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE
          R.γbar N)
    (hM : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M)
    (hN : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) N)
    (f : M →ₗ[R.polyD] N) :
    ConnectionPairOverSmooth.Hom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
      (baseChangeNablaAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hM nablaM)
      (baseChangeNablaAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hN nablaN) :=
  { toLinearMap := baseChangeCarrierA.map p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f
    commutes := sorry }

/-- Completed base change of a `D'`-linear map along `b`, as a morphism of polynomial pairs. -/
noncomputable def mapHomAlongB
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R.smoothD M] [Module R.smoothD N]
    {nablaM : M →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M}
    {nablaN : N →+ completedTensorOf p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N}
    {hBaseM :
      IsAdicComplete (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)}
    {hBaseN :
      IsAdicComplete (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N)}
    {hM : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M}
    {hN : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) N}
    (hIntM : integrableAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M nablaM hM hBaseM)
    (hIntN : integrableAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N nablaN hN hBaseN)
    (hNilM : quasiNilpotentAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M nablaM hM hBaseM)
    (hNilN : quasiNilpotentAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R N nablaN hN hBaseN)
    (f : M →ₗ[R.smoothD] N) :
    CrystallineConnectionPair.Hom p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
      { isAdicComplete := hBaseM
        nabla := @baseChangeNablaAlongB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
          R M _ _ hM nablaM
        leibniz := sorry
        isIntegrable := hIntM
        isTopologicallyQuasiNilpotent := hNilM }
      { isAdicComplete := hBaseN
        nabla := @baseChangeNablaAlongB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
          R N _ _ hN nablaN
        leibniz := sorry
        isIntegrable := hIntN
        isTopologicallyQuasiNilpotent := hNilN } :=
  Hom.of p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar
    (baseChangeCarrierB.map p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f)

/-- Functoriality of completed base change along `a` on bundled polynomial pairs. -/
noncomputable def mapPairAlongA
    {P Q : ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar}
    (f : P ⟶ Q) :=
  -- Local instance justification (proof-local temporary data):
  -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
  letI := P.addCommGroup
  letI := P.module
  letI := Q.addCommGroup
  letI := Q.module
  @mapHomAlongA A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
    R P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module
    (@CrystallineConnectionPair.nabla A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ R.J R.hJ
      hIC hpnil R.hIJ R.E R.hE R.γbar P.M P.addCommGroup P.module P.pair)
    (@CrystallineConnectionPair.nabla A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ R.J R.hJ
      hIC hpnil R.hIJ R.E R.hE R.γbar Q.M Q.addCommGroup Q.module Q.pair)
    (@CrystallineConnectionPair.isAdicComplete A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ
      R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar P.M P.addCommGroup P.module P.pair)
    (@CrystallineConnectionPair.isAdicComplete A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ
      R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar Q.M Q.addCommGroup Q.module Q.pair)
    (@Hom.toLinearMap A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ R.J R.hJ hIC hpnil
      R.hIJ R.E R.hE R.γbar P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module
      P.pair Q.pair f)

/-- The category of completed connection pairs over `D'`. -/
noncomputable instance connectionPairOverSmoothCategory :
    Category (ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) where
  Hom P Q :=
    @ConnectionPairOverSmooth.Hom A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
      R P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module P.nabla Q.nabla
  id P :=
    @ConnectionPairOverSmooth.Hom.id A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
      R P.M P.addCommGroup P.module P.nabla
  comp {P Q S} f g :=
    @ConnectionPairOverSmooth.Hom.comp A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
      R P.M Q.M S.M P.addCommGroup Q.addCommGroup S.addCommGroup P.module Q.module S.module
      P.nabla Q.nabla S.nabla f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Functoriality of completed base change along `b` on bundled pairs over `D'`. -/
noncomputable def mapPairAlongB
    {P Q : ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R}
    (f : P ⟶ Q) :=
  @mapHomAlongB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
    R P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module P.nabla Q.nabla
    P.baseChangeComplete Q.baseChangeComplete P.isAdicComplete Q.isAdicComplete
    P.isIntegrable Q.isIntegrable
    P.isTopologicallyQuasiNilpotent Q.isTopologicallyQuasiNilpotent
    (@ConnectionPairOverSmooth.Hom.toLinearMap A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ'
      hIC hpnil hIJ' E' hE' _ R P.M Q.M P.addCommGroup Q.addCommGroup P.module Q.module
      P.nabla Q.nabla f)

/-- Base-change functor `F` along `a`, from polynomial pairs to pairs over `D'`. -/
noncomputable def baseChangeAlongA :
    ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar ⥤
      ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R where
  obj P :=
    -- Local instance justification (proof-local temporary data):
    -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
    letI := P.addCommGroup
    letI := P.module
    @ConnectionPairOverSmooth.of A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
      R (@baseChangeCarrierA A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R P.M P.addCommGroup P.module)
      (@baseChangeCarrierA.addCommGroup A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R P.M P.addCommGroup P.module)
      (@baseChangeCarrierA.moduleSmooth A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R P.M P.addCommGroup P.module)
      (sorry :
        IsAdicComplete (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
          (@baseChangeCarrierA A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
            R P.M P.addCommGroup P.module))
      (@baseChangeNablaAlongA A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R P.M P.addCommGroup P.module
        (@CrystallineConnectionPair.isAdicComplete A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π
          R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar P.M P.addCommGroup P.module P.pair)
        (@CrystallineConnectionPair.nabla A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ R.J
          R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar P.M P.addCommGroup P.module P.pair))
      sorry sorry sorry sorry
  map {P Q} f :=
    mapPairAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f
  map_id := sorry
  map_comp := sorry

/-- Object carrier of `baseChangeAlongA` is the completed tensor along `a`. -/
theorem baseChangeAlongA_obj_carrier
    (P : ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar) :
    ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P).M =
      @baseChangeCarrierA A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R P.M P.addCommGroup P.module :=
  sorry

/-- Base-change functor `G` along `b`, from pairs over `D'` to polynomial pairs. -/
noncomputable def baseChangeAlongB :
    ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⥤
      ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar where
  obj Q :=
    @ConnectionPairCat.of A _ p _ _ I γ C _ _ (polynomialIndex R.n) R.π R.hπ R.J R.hJ hIC hpnil
      R.hIJ R.E R.hE R.γbar
      (@baseChangeCarrierB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R Q.M Q.addCommGroup Q.module)
      (@baseChangeCarrierB.addCommGroup A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ'
        E' hE' _ R Q.M Q.addCommGroup Q.module)
      (@baseChangeCarrierB.modulePoly A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ'
        E' hE' _ R Q.M Q.addCommGroup Q.module)
      { isAdicComplete := Q.baseChangeComplete
        nabla :=
          @baseChangeNablaAlongB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
            R Q.M Q.addCommGroup Q.module Q.isAdicComplete Q.nabla
        leibniz := sorry
        isIntegrable := Q.isIntegrable
        isTopologicallyQuasiNilpotent := Q.isTopologicallyQuasiNilpotent }
  map {P Q} f :=
    mapPairAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R f
  map_id := sorry
  map_comp := sorry

/-- Object carrier of `baseChangeAlongB` is the completed tensor along `b`. -/
theorem baseChangeAlongB_obj_carrier
    (Q : ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) :
    ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q).M =
      @baseChangeCarrierB A _ p _ _ I γ C _ _ P' _ _ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' _
        R Q.M Q.addCommGroup Q.module :=
  sorry

/-- Contraction `M' ⊗_{D'} D → M'` along `a : D → D'`. -/
noncomputable def contractTensorB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M] :
    baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+ M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  TensorProduct.liftAddHom
    (M := M) (N := R.polyD) (P := M) (R := R.smoothD)
    { toFun := fun m =>
        { toFun := fun d => R.a d • m
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- Continuous extension of `contractTensorB` from the `p`-adic completion along `b`. -/
noncomputable def contractCarrierB
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M) :
    baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+ M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- restriction of scalars along `a` makes `M` a complete `D`-module so that
  -- `AdicCompletion.map` can extend the tensor contraction.
  letI : Module R.polyD M :=
    Module.compHom M R.a
  letI : IsScalarTower R.polyD R.smoothD M := sorry
  letI : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M :=
    sorry
  let f :
      baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.polyD] M :=
    { toFun := fun t =>
        contractTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R t
      map_add' := sorry
      map_smul' := sorry }
  AddMonoidHom.mk'
    (fun y =>
      (AdicCompletion.ofLinearEquiv
          (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M).symm
        (AdicCompletion.map
          (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) f y))
    sorry

/-- Uncompleted reassociation `(M' ⊗^∧_{D', b} D) ⊗[D, a] D' → M'` along `a ∘ b = id`. -/
noncomputable def reassociateFromTensorA
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M) :
    baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) →ₗ[R.smoothD] M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- bundled completeness of `M` is required to contract the inner completion.
  letI := hComplete
  { toFun :=
      TensorProduct.liftAddHom
        (M := baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
        (N := R.smoothD) (P := M) (R := R.polyD)
        { toFun := fun y =>
            { toFun := fun d' =>
                d' • contractCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete y
              map_zero' := sorry
              map_add' := sorry }
          map_zero' := sorry
          map_add' := sorry }
        sorry
    map_add' := sorry
    map_smul' := sorry }

/-- Completed tensor reassociation `(M' ⊗^∧_{D', b} D) ⊗^∧_{D, a} D' → M'` induced by
`a ∘ b = id_{D'}`. -/
noncomputable def reassociateAlongRetract
    {M : Type u} [AddCommGroup M] [Module R.smoothD M]
    (hComplete : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M) :
    baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
        (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) →ₗ[R.smoothD] M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- `ofLinearEquiv` needs completeness of the `D'`-module.
  letI := hComplete
  { toFun := fun x =>
      (AdicCompletion.ofLinearEquiv
          (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M).symm
        (AdicCompletion.map
          (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
          (reassociateFromTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete) x)
    map_add' := sorry
    map_smul' := sorry }

/-- Completed tensor reassociation `(M' ⊗^∧_{D', b} D) ⊗^∧_{D, a} D' → M'` induced by
`a ∘ b = id_{D'}`. -/
noncomputable def baseChangeSectionHom
    (Q : ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) :
    ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q) ⟶ Q :=
  -- Local instance justification (proof-local temporary data):
  -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
  letI := Q.addCommGroup
  letI := Q.module
  letI := ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q).addCommGroup
  letI := ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q).module
  letI := Q.isAdicComplete
  { toLinearMap :=
      { toFun := fun x =>
          reassociateAlongRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q.isAdicComplete
            (x : baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
              (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q.M))
        map_add' := sorry
        map_smul' := sorry }
    commutes := sorry }

/-- The inverse reassociation `M' → (M' ⊗^∧_{D', b} D) ⊗^∧_{D, a} D'`. -/
noncomputable def baseChangeSectionInv
    (Q : ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) :
    Q ⟶ ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
  letI := Q.addCommGroup
  letI := Q.module
  letI := ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q).addCommGroup
  letI := ((baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj Q).module
  { toLinearMap :=
      { toFun := fun m =>
          AdicCompletion.of
            (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
            (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
              (baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q.M))
            ((AdicCompletion.of
                (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
                (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q.M)
                (m ⊗ₜ[R.smoothD] (1 : R.polyD))) ⊗ₜ[R.polyD] (1 : R.smoothD))
        map_add' := sorry
        map_smul' := sorry }
    commutes := sorry }

/-- Since `a ∘ b = id_{D'}`, base change along `b` followed by base change along `a`
is isomorphic to the identity on pairs over `D'`. -/
noncomputable def baseChange_section_id :
    baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ≅
      𝟭 (ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) :=
  NatIso.ofComponents
    (fun Q =>
      { hom := baseChangeSectionHom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q
        inv := baseChangeSectionInv p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R Q
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The section components are mutually inverse. -/
theorem baseChange_section_id_hom_inv
    (Q : ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) :
    (baseChange_section_id p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).inv.app Q ≫
        (baseChange_section_id p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).hom.app Q =
      𝟙 Q :=
  sorry

/-- Contraction `(M ⊗_{D, a} D') → M` along `b : D' → D`. -/
noncomputable def contractTensorA
    {M : Type u} [AddCommGroup M] [Module R.polyD M] :
    baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+ M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  TensorProduct.liftAddHom
    (M := M) (N := R.smoothD) (P := M) (R := R.polyD)
    { toFun := fun m =>
        { toFun := fun d' => R.b d' • m
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- Continuous extension of `contractTensorA` from the `p`-adic completion along `a`. -/
noncomputable def contractCarrierA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M) :
    baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →+ M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- restriction of scalars along `b` makes `M` a complete `D'`-module so that
  -- `AdicCompletion.map` can extend the tensor contraction.
  letI : Module R.smoothD M :=
    Module.compHom M R.b
  letI : IsScalarTower R.smoothD R.polyD M := sorry
  letI : IsAdicComplete
      (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M :=
    sorry
  let f :
      baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M →ₗ[R.smoothD] M :=
    { toFun := fun t =>
        contractTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R t
      map_add' := sorry
      map_smul' := sorry }
  AddMonoidHom.mk'
    (fun y =>
      (AdicCompletion.ofLinearEquiv
          (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) M).symm
        (AdicCompletion.map
          (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R) f y))
    sorry

/-- Uncompleted reassociation `(M ⊗^∧_{D, a} D') ⊗[D', b] D → M` along `b ∘ a`. -/
noncomputable def reassociateFromTensorB
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M) :
    baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
        (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) →ₗ[R.polyD] M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- bundled completeness of `M` is required to contract the inner completion.
  letI := hComplete
  { toFun :=
      TensorProduct.liftAddHom
        (M := baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M)
        (N := R.polyD) (P := M) (R := R.smoothD)
        { toFun := fun y =>
            { toFun := fun d =>
                d • contractCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete y
              map_zero' := sorry
              map_add' := sorry }
          map_zero' := sorry
          map_add' := sorry }
        sorry
    map_add' := sorry
    map_smul' := sorry }

/-- Completed reassociation `(M ⊗^∧_{D, a} D') ⊗^∧_{D', b} D → M` along `b ∘ a`. -/
noncomputable def reassociateAlongBA
    {M : Type u} [AddCommGroup M] [Module R.polyD M]
    (hComplete : IsAdicComplete
      (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M) :
    baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
        (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R M) →ₗ[R.polyD] M :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- `ofLinearEquiv` needs completeness of the polynomial module.
  letI := hComplete
  { toFun := fun x =>
      (AdicCompletion.ofLinearEquiv
          (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE) M).symm
        (AdicCompletion.map
          (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
          (reassociateFromTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R hComplete) x)
    map_add' := sorry
    map_smul' := sorry }

/-- The comparison morphism of Proposition 60.17.4 along `id_D` and `b ∘ a`,
on quasi-nilpotent pairs over `D`. -/
noncomputable def baseChangeRetractHom
    (P : ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar) :
    ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P) ⟶ P :=
  -- Local instance justification (proof-local temporary data):
  -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
  letI := P.addCommGroup
  letI := P.module
  letI := ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P).addCommGroup
  letI := ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P).module
  letI := P.pair.isAdicComplete
  { toLinearMap :=
      { toFun := fun x =>
          reassociateAlongBA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P.pair.isAdicComplete
            (x : baseChangeCarrierB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
              (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P.M))
        map_add' := sorry
        map_smul' := sorry }
    commutes := sorry }

/-- The inverse comparison `M → (M ⊗^∧_{D, a} D') ⊗^∧_{D', b} D`. -/
noncomputable def baseChangeRetractInv
    (P : ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar) :
    P ⟶ ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P) :=
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.polyD R.smoothD :=
    algebraAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (noncanonical choice): competing Algebra along a vs b
  letI : Algebra R.smoothD R.polyD :=
    algebraAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
  -- Local instance justification (proof-local temporary data):
  -- bundled pairs store `AddCommGroup`/`Module` as fields, not instances.
  letI := P.addCommGroup
  letI := P.module
  letI := ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P).addCommGroup
  letI := ((baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
      baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).obj P).module
  { toLinearMap :=
      { toFun := fun m =>
          AdicCompletion.of
            (crystallineD.pIdeal p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
            (baseChangeTensorB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R
              (baseChangeCarrierA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P.M))
            ((AdicCompletion.of
                (crystallineDOf.pIdeal p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R)
                (baseChangeTensorA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P.M)
                (m ⊗ₜ[R.polyD] (1 : R.smoothD))) ⊗ₜ[R.smoothD] (1 : R.polyD))
        map_add' := sorry
        map_smul' := sorry }
    commutes := sorry }

/-- On quasi-nilpotent pairs over `D`, completed base change along `a` followed by
base change along `b` is isomorphic to the identity, via the comparison `c_{id_D, b ∘ a}`
of Proposition 60.17.4. -/
noncomputable def baseChange_retract_id :
    baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ⋙
        baseChangeAlongB p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R ≅
      𝟭 (ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar) :=
  NatIso.ofComponents
    (fun P =>
      { hom := baseChangeRetractHom p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P
        inv := baseChangeRetractInv p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R P
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The retract comparison components are mutually inverse. -/
theorem baseChange_retract_id_hom_inv
    (P : ConnectionPairCat p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar) :
    (baseChange_retract_id p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).inv.app P ≫
        (baseChange_retract_id p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R).hom.app P =
      𝟙 P :=
  sorry

end CrystallineConnectionPair

namespace CrystallineModuleSheaf

/-- Evaluation of crystals as pairs over the smooth completed envelope `D'`. -/
noncomputable def crystalsToConnectionPairsOverSmooth
    {S : Scheme.{u}} {IS : S.IdealSheafData}
    {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    QuasiCoherentCrystal S IS γS h_compatible X x₀ ⥤
      CrystallineConnectionPair.ConnectionPairOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'
        R :=
  crystalsToConnectionPairs p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar T moduleT ⋙
    CrystallineConnectionPair.baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R

/-- The crystals functor towards pairs over `D'` is the polynomial functor of
Proposition 60.17.4 composed with completed base change along `a`. -/
theorem crystalsToConnectionPairsOverSmooth_eq
    {S : Scheme.{u}} {IS : S.IdealSheafData}
    {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    crystalsToConnectionPairsOverSmooth p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R T moduleT =
      crystalsToConnectionPairs p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE R.γbar T
          moduleT ⋙
        CrystallineConnectionPair.baseChangeAlongA p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' R :=
  sorry

end CrystallineModuleSheaf

end
