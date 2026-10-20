/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import stacks_project.Chap60.«60_17_0_1»
public import stacks_project.Chap60.«60_17_0_2»
public import stacks_project.Chap60.«60_17_0_3»
public import stacks_project.Chap60.Remark_60_6_8_Connection

@[expose] public section

open scoped TensorProduct

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : Ideal (MvPolynomial ι A))
variable (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial ι A)) hIJ E)

/-- The canonical ring map from `A` into the completed envelope `D`. -/
noncomputable def crystallineDBaseMap :
    A →+* crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE :=
  (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)).comp
    (E.toD.comp (algebraMap A (MvPolynomial ι A)))

/-- The `A`-algebra structure on the completed envelope `D`. -/
noncomputable instance crystallineD.algebra :
    Algebra A (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) :=
  (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE).toAlgebra

/-- Unfolding of the base map into the completed envelope. -/
theorem crystallineDBaseMap_comp :
    crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE =
      (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)).comp
        (E.toD.comp (algebraMap A (MvPolynomial ι A))) :=
  sorry

variable (γbar : DividedPowers
  (Ideal.map (algebraMap E.D (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE))
    E.D.ideal))

/-- The `p`-adic ideal of the completed envelope `D`. -/
noncomputable def crystallineD.pIdeal :
    Ideal (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) :=
  Ideal.span {(p : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)}

/-- Unfolding of the `p`-adic ideal of `D`. -/
theorem crystallineD.pIdeal_eq :
    crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE =
      Ideal.span {(p : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)} :=
  sorry

/-- The image of a polynomial coordinate `x_i` in the completed envelope `D`. -/
noncomputable def crystallineD.X (i : ι) :
    crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE :=
  AdicCompletion.of (Ideal.span {(p : E.D)}) E.D (E.toD (MvPolynomial.X i))

/-- Unfolding of the image of `x_i` in `D`. -/
theorem crystallineD.X_eq (i : ι) :
    crystallineD.X p I γ π hπ J hJ hIC hpnil hIJ E hE i =
      AdicCompletion.of (Ideal.span {(p : E.D)}) E.D (E.toD (MvPolynomial.X i)) :=
  sorry

/-- The completed coordinate differential `d x_i` in `Ω_D`. -/
noncomputable def crystallineOmegaD.dX (i : ι) :
    crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p :=
  crystallineOmegaD_derivation
    (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p
    (crystallineD.X p I γ π hπ J hJ hIC hpnil hIJ E hE i)

/-- The family `d x_i` is linearly independent over `D`. -/
theorem crystallineOmegaD.dX_linearIndependent :
    LinearIndependent (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (crystallineOmegaD.dX p I γ π hπ J hJ hIC hpnil hIJ E hE γbar) :=
  sorry

/-- The family `d x_i` spans `Ω_D` after completion. -/
theorem crystallineOmegaD.dX_span :
    (⊤ : Submodule (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
          γbar p)) ≤
      Submodule.span (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (Set.range (crystallineOmegaD.dX p I γ π hπ J hJ hIC hpnil hIJ E hE γbar)) :=
  sorry

/-- The completed free basis of `Ω_D` on the coordinate differentials `d x_i`. -/
noncomputable def crystallineOmegaD.basis :
    Module.Basis ι (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
        γbar p) :=
  Module.Basis.mk (crystallineOmegaD.dX_linearIndependent p I γ π hπ J hJ hIC hpnil hIJ E hE γbar)
    (crystallineOmegaD.dX_span p I γ π hπ J hJ hIC hpnil hIJ E hE γbar)

/-- Coefficient of `d x_i` on `Ω_D`. -/
noncomputable def crystallineOmegaD.coord (i : ι) :
    crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
      crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE :=
  (crystallineOmegaD.basis p I γ π hπ J hJ hIC hpnil hIJ E hE γbar).coord i

/-- The completed tensor `M ⊗^∧_D Ω_D` appearing as the codomain of `∇`. -/
noncomputable def CrystallineConnectionPair.completedTensor
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] : Type u :=
  AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
      crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p)

/-- Unfolding of the completed tensor as an adic completion. -/
theorem CrystallineConnectionPair.completedTensor_eq
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] :
    CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M =
      AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
          crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
            γbar p) :=
  sorry

/-- Additive group structure on the completed tensor. -/
noncomputable instance completedTensor.addCommGroup
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] :
    AddCommGroup
      (CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M) :=
  inferInstanceAs
    (AddCommGroup
      (AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
          crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
            γbar p)))

/-- `D`-module structure on the completed tensor. -/
noncomputable instance completedTensor.module
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] :
    Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M) :=
  inferInstanceAs
    (Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
          crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
            γbar p)))

/-- Canonical map from the uncompleted tensor into the completed tensor. -/
noncomputable def CrystallineConnectionPair.completedTensor.of
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] :
    M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
        crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
          γbar p →+
      CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M :=
  AddMonoidHom.mk'
    (fun ω ↦
      AdicCompletion.of (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
          crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
            γbar p) ω)
    sorry

/-- Functoriality of completed tensors in the module variable. -/
noncomputable def CrystallineConnectionPair.completedTensor.map
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) N]
    (f : M →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE] N) :
    CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M →+
      CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar N :=
  (AdicCompletion.map (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (TensorProduct.map f
      (LinearMap.id
        (R := crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (M := crystallineOmegaD
          (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p)))).toAddMonoidHom

/-- Coefficient of `d x_i` on an uncompleted tensor `M ⊗_D Ω_D`. -/
noncomputable def CrystallineConnectionPair.completedTensor.uncompletedCoord
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] (i : ι) :
    M ⊗[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
        crystallineOmegaD (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE)
          γbar p →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE] M :=
  (TensorProduct.rid (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M).toLinearMap.comp
    (LinearMap.lTensor M
      (crystallineOmegaD.coord p I γ π hπ J hJ hIC hpnil hIJ E hE γbar i))

/-- Coefficient of `d x_i` after `p`-adic completion of `M ⊗_D Ω_D`. -/
noncomputable def CrystallineConnectionPair.completedTensor.coord
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] (i : ι) :
    CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
      AdicCompletion (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M :=
  (AdicCompletion.map (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE)
    (CrystallineConnectionPair.completedTensor.uncompletedCoord p I γ π hπ J hJ
      hIC hpnil hIJ E hE γbar M i)).restrictScalars
    (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)

/-- Coordinate operator `θ_i` associated to a completed connection map. -/
noncomputable def connectionPartialOf
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (hComplete :
      IsAdicComplete (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M)
    (nabla :
      M →+
        CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
          γbar M)
    (i : ι) : M →+ M :=
  -- Local instance justification (proof-local temporary data):
  -- `ofLinearEquiv` needs the pair's completeness field as an instance.
  letI := hComplete
  (AdicCompletion.ofLinearEquiv
      (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M).symm.toAddMonoidHom.comp
    ((CrystallineConnectionPair.completedTensor.coord p I γ π hπ J hJ hIC hpnil hIJ
        E hE γbar M i).toAddMonoidHom.comp nabla)

/-- A pair `(M, ∇)` of a `p`-adically complete `D`-module and a completed
connection `∇ : M → M ⊗^∧_D Ω_D` satisfying (07JB)–(07JE). -/
structure CrystallineConnectionPair
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M] where
  /-- `p`-adic completeness of `M` (07JB). -/
  isAdicComplete :
    IsAdicComplete (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M
  /-- The additive connection map into the completed tensor. -/
  nabla :
    M →+
      CrystallineConnectionPair.completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE
        γbar M
  /-- The Leibniz identity for `∇` against `d : D → Ω_D` (07JC). -/
  leibniz :
    ∀ (b : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) (m : M),
      nabla (b • m) =
        b • nabla m +
          CrystallineConnectionPair.completedTensor.of p I γ π hπ J hJ hIC hpnil hIJ
              E hE γbar M
            (m ⊗ₜ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
              crystallineOmegaD_derivation
                (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p b)
  /-- Integrability (07JD): the coordinate operators `θ_i` commute. -/
  isIntegrable : ∀ (i j : ι),
    (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M isAdicComplete nabla i).comp
        (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M isAdicComplete nabla j) =
      (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M isAdicComplete nabla j).comp
        (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M isAdicComplete nabla i)
  /-- Topological quasi-nilpotence of the coordinate operators `θ_i` (07JE). -/
  isTopologicallyQuasiNilpotent : ∀ (m : M) (i : ι),
    Set.Finite
      {k : ℕ |
        (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
            isAdicComplete nabla i)^[k] m ∉
          (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE •
            (⊤ : Submodule (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M))}

namespace CrystallineConnectionPair

/-- Smart constructor for a completed connection pair from its connection map. -/
noncomputable def of
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (nabla :
      M →+
        completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M :=
  { isAdicComplete := sorry
    nabla := nabla
    leibniz := sorry
    isIntegrable := sorry
    isTopologicallyQuasiNilpotent := sorry }

/-- The smart constructor retains the supplied connection map. -/
theorem of_nabla
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (nabla :
      M →+
        completedTensor p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    (of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M nabla).nabla = nabla :=
  sorry

/-- Completeness clause (07JB) of a completed connection pair. -/
theorem spec_complete
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    IsAdicComplete (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M :=
  P.isAdicComplete

/-- Leibniz clause (07JC) of a completed connection pair. -/
theorem spec_leibniz
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (b : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) (m : M) :
    P.nabla (b • m) =
      b • P.nabla m +
        completedTensor.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
          (m ⊗ₜ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
            crystallineOmegaD_derivation
              (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p b) :=
  P.leibniz b m

/-- Integrability clause (07JD) of a completed connection pair. -/
theorem spec_integrable
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (i j : ι) :
    (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
          P.isAdicComplete P.nabla i).comp
        (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
          P.isAdicComplete P.nabla j) =
      (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
          P.isAdicComplete P.nabla j).comp
        (connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
          P.isAdicComplete P.nabla i) :=
  P.isIntegrable i j

/-- Coordinate operators `θ_i` determined by `∇(m) = ∑ θ_i(m) dx_i`. -/
noncomputable def connectionPartial
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (i : ι) : M →+ M :=
  connectionPartialOf p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M P.isAdicComplete P.nabla i

/-- Source-semantic bundle of (07JB)–(07JE) for a completed connection pair. -/
theorem spec
    (M : Type u) [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    IsAdicComplete (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE) M ∧
      (∀ (b : crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) (m : M),
        P.nabla (b • m) =
          b • P.nabla m +
            completedTensor.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
              (m ⊗ₜ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
                crystallineOmegaD_derivation
                  (crystallineDBaseMap p I γ π hπ J hJ hIC hpnil hIJ E hE) γbar p b)) ∧
      (∀ (i j : ι),
        (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P i).comp
            (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P j) =
          (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P j).comp
            (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P i)) ∧
      (∀ (m : M) (i : ι),
        Set.Finite
          {k : ℕ |
            (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P i)^[k] m ∉
              (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE •
                (⊤ : Submodule
                  (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M))}) :=
  sorry

/-- The operators `θ_i` recover the completed connection in coordinates. -/
theorem connectionPartial_spec
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    [Fintype ι]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (m : M) :
    P.nabla m =
      completedTensor.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M
        (∑ i : ι,
          connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P i m ⊗ₜ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE]
            crystallineOmegaD.dX p I γ π hπ J hJ hIC hpnil hIJ E hE γbar i) :=
  sorry

/-- Topological quasi-nilpotence as finiteness of `{k | θ_i^[k](m) ∉ pM}`. -/
theorem isTopologicallyQuasiNilpotent_apply
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (m : M) (i : ι) :
    Set.Finite
      {k : ℕ |
        (connectionPartial p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P i)^[k] m ∉
          (crystallineD.pIdeal p I γ π hπ J hJ hIC hpnil hIJ E hE •
            (⊤ : Submodule (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M))} :=
  P.isTopologicallyQuasiNilpotent m i

/-- Morphisms of completed connection pairs: maps of modules commuting with `∇`. -/
structure Hom
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) N]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M)
    (Q : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar N) where
  /-- The underlying `D`-linear map. -/
  toLinearMap : M →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE] N
  /-- Commutation with the completed connections. -/
  commutes (m : M) :
    Q.nabla (toLinearMap m) =
      completedTensor.map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar toLinearMap
        (P.nabla m)

/-- Identity morphism of a completed connection pair. -/
noncomputable def Hom.id
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P P :=
  { toLinearMap := LinearMap.id
    commutes := sorry }

/-- Construct a pair morphism from a `D`-linear map. -/
noncomputable def Hom.of
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) N]
    {P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M}
    {Q : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar N}
    (f : M →ₗ[crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE] N) :
    Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P Q :=
  { toLinearMap := f
    commutes := sorry }

/-- Composition of morphisms of completed connection pairs. -/
noncomputable def Hom.comp
    {M N Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) N]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) Q]
    {X : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M}
    {Y : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar N}
    {Z : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar Q}
    (f : Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar X Y)
    (g : Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar Y Z) :
    Hom p I γ π hπ J hJ hIC hpnil hIJ E hE γbar X Z :=
  Hom.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar (g.toLinearMap.comp f.toLinearMap)

/-- The identity morphism is the identity linear map. -/
theorem Hom.id_toLinearMap
    {M : Type u} [AddCommGroup M]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE) M]
    (P : CrystallineConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar M) :
    (Hom.id p I γ π hπ J hJ hIC hpnil hIJ E hE γbar P).toLinearMap = LinearMap.id :=
  sorry

end CrystallineConnectionPair
