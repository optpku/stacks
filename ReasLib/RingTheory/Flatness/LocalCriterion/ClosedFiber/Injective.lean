/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.LinearMap.Ladder
public import ReasLib.LinearAlgebra.QuotientByIdeal.Reduction
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor
public import ReasLib.RingTheory.LocalRing.Quotient

/-!
# Closed-Fiber Injectivity over a Local Ring

@stack 00ME

This leaf owns the linear-map half of the closed-fiber local criterion.  It
propagates injectivity from the closed fiber through the maximal-ideal power
filtration and finishes with Krull intersection on the finite source module.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace LinearMap.ClosedFiber

variable {R : Type u} {S : Type v} {M N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S]
variable [AddCommGroup M] [Module R M] [Module.Flat R M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N]

omit [IsLocalRing R] in
/-- Injectivity after right tensoring with the two ends of a short exact row
propagates to the middle when the target module is flat. -/
theorem rTensor_injective_of_shortExact
    {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [Module.Flat R Q]
    (f : P →ₗ[R] Q)
    {Q₁ Q₂ Q₃ : Type*}
    [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂]
    [AddCommGroup Q₃] [Module R Q₃]
    {i : Q₁ →ₗ[R] Q₂} {π : Q₂ →ₗ[R] Q₃}
    (hi : Function.Injective i) (hExact : Function.Exact i π)
    (hπ : Function.Surjective π)
    (hQ₁ : Function.Injective (f.rTensor Q₁))
    (hQ₃ : Function.Injective (f.rTensor Q₃)) :
    Function.Injective (f.rTensor Q₂) := by
  intro x y hxy
  let d : TensorProduct R P Q₂ := x - y
  have hdQ₃ : (π.lTensor P) d = 0 := by
    apply hQ₃
    calc
      (f.rTensor Q₃) ((π.lTensor P) d) =
          ((π.lTensor Q).comp (f.rTensor Q₂)) d := by
            rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
              LinearMap.lTensor_comp_rTensor]
      _ = 0 := by
        change ((π.lTensor Q).comp (f.rTensor Q₂)) (x - y) = 0
        rw [LinearMap.comp_apply, map_sub, hxy, sub_self]
        simp
  obtain ⟨z, hz⟩ := ((_root_.lTensor_exact P hExact hπ) d).mp hdQ₃
  have hiTensor : Function.Injective (i.lTensor Q) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hfd : (f.rTensor Q₂) d = 0 := by
    change (f.rTensor Q₂) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzTensor : (f.rTensor Q₁) z = 0 := by
    apply hiTensor
    calc
      (i.lTensor Q) ((f.rTensor Q₁) z) =
          ((f.rTensor Q₂).comp (i.lTensor P)) z := by
            change ((i.lTensor Q).comp (f.rTensor Q₁)) z =
              ((f.rTensor Q₂).comp (i.lTensor P)) z
            rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (f.rTensor Q₂) d := by rw [LinearMap.comp_apply, hz]
      _ = 0 := hfd
  have hzZero : z = 0 := hQ₁ hzTensor
  have hdZero : d = 0 := by simpa [hzZero] using hz.symm
  simpa [d, sub_eq_zero] using hdZero

/-- Tensoring a module over the residue field depends only on the closed-fiber
quotient of the other tensor factor. -/
noncomputable def tensorLinearEquiv
    {P : Type*} [AddCommGroup P] [Module R P]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    TensorProduct R Q P ≃ₗ[R]
      TensorProduct (R ⧸ maximalIdeal R) Q
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
  let eQuot :
      TensorProduct R (R ⧸ maximalIdeal R) P ≃ₗ[R ⧸ maximalIdeal R]
        (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R)).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eTensor :
      TensorProduct (R ⧸ maximalIdeal R) Q
          (TensorProduct R (R ⧸ maximalIdeal R) P) ≃ₗ[R ⧸ maximalIdeal R]
        TensorProduct (R ⧸ maximalIdeal R) Q
          (P ⧸ ((maximalIdeal R) • (⊤ : Submodule R P))) :=
    eQuot.lTensor Q
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ maximalIdeal R)
    (R ⧸ maximalIdeal R) Q P).symm.trans eTensor).restrictScalars R

/-- The closed-fiber tensor comparison on pure tensors. -/
@[simp]
theorem tensorLinearEquiv_tmul
    {P : Type*} [AddCommGroup P] [Module R P]
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q]
    (q : Q) (x : P) :
    tensorLinearEquiv (R := R) (P := P) Q (q ⊗ₜ[R] x) =
      q ⊗ₜ[R ⧸ maximalIdeal R] (Submodule.Quotient.mk x) := by
  simp [tensorLinearEquiv]

/-- Naturality of the inverse closed-fiber tensor comparison. -/
theorem tensorLinearEquiv_symm_naturality
    {P P' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    (f : P →ₗ[R] P')
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    (f.lTensor Q).comp
        (tensorLinearEquiv (R := R) (P := P) Q).symm.toLinearMap =
      (tensorLinearEquiv (R := R) (P := P') Q).symm.toLinearMap.comp
        ((((f.reduceModIdeal (maximalIdeal R)).lTensor Q)).restrictScalars R) := by
  apply DFunLike.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro q xbar
    obtain ⟨x, rfl⟩ :=
      Submodule.mkQ_surjective ((maximalIdeal R) • (⊤ : Submodule R P)) xbar
    simp [tensorLinearEquiv]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Closed-fiber injectivity implies injectivity after tensoring with every
module over the residue field. -/
theorem rTensor_injective_of_mod_maximalIdeal_injective
    {P P' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup P'] [Module R P']
    (f : P →ₗ[R] P')
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R)))
    (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module (R ⧸ maximalIdeal R) Q] [IsScalarTower R (R ⧸ maximalIdeal R) Q] :
    Function.Injective (f.rTensor Q) := by
  have hReduce :
      Function.Injective (((f.reduceModIdeal (maximalIdeal R))).restrictScalars R) := by
    simpa [LinearMap.quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
      (R := R) f (maximalIdeal R)] using hf
  have hTensorReduce : Function.Injective
      ((((f.reduceModIdeal (maximalIdeal R)).lTensor Q)).restrictScalars R) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    letI : Module.Free (R ⧸ maximalIdeal R) Q :=
      Module.Free.of_divisionRing (R ⧸ maximalIdeal R) Q
    letI : Module.Flat (R ⧸ maximalIdeal R) Q := Module.Flat.of_free
    exact Module.Flat.lTensor_preserves_injective_linearMap
      ((f.reduceModIdeal (maximalIdeal R))) hReduce
  have hTensor : Function.Injective (f.lTensor Q) :=
    LinearMap.injective_of_ladder_linearEquiv (R := R)
      (tensorLinearEquiv_symm_naturality (R := R) (P := P) (P' := P') f Q)
      hTensorReduce
  simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hTensor

/-- The canonical maximal-ideal power row is short exact. -/
theorem maximalIdeal_pow_successor_exact
    (n : ℕ) :
    let m : Ideal R := maximalIdeal R
    let K : Ideal (R ⧸ (m ^ (n + 1))) :=
      Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) (m ^ n)
    let Q₁ : Type u :=
      ((m ^ n : Ideal R) ⧸ (m • (⊤ : Submodule R (m ^ n : Ideal R))))
    let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)) :=
      (((K.restrictScalars R).subtype).comp
        (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m n).toLinearMap :
          Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)))
    let π : R ⧸ (m ^ (n + 1)) →ₗ[R] R ⧸ (m ^ n) :=
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).toLinearMap
    Function.Injective i ∧ Function.Exact i π ∧ Function.Surjective π := by
  let m : Ideal R := maximalIdeal R
  let K : Ideal (R ⧸ (m ^ (n + 1))) :=
    Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) (m ^ n)
  let Q₁ : Type u :=
    ((m ^ n : Ideal R) ⧸ (m • (⊤ : Submodule R (m ^ n : Ideal R))))
  let Ksub : Submodule R (R ⧸ (m ^ (n + 1))) :=
    (K : Submodule (R ⧸ (m ^ (n + 1))) (R ⧸ (m ^ (n + 1)))).restrictScalars R
  let e : Q₁ ≃ₗ[R] K := Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m n
  let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 1)) := (Ksub.subtype).comp e.toLinearMap
  let π : R ⧸ (m ^ (n + 1)) →ₗ[R] R ⧸ (m ^ n) :=
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).toLinearMap
  dsimp only
  constructor
  · exact Ksub.subtype_injective.comp e.injective
  constructor
  · have hkerIdeal :
        RingHom.ker (Ideal.Quotient.factorₐ R
          (Ideal.pow_le_pow_right n.le_succ)) = K := by
      change RingHom.ker (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right n.le_succ)) = K
      exact Ideal.Quotient.factor_ker (I := m ^ (n + 1)) (J := m ^ n)
        (Ideal.pow_le_pow_right n.le_succ)
    have hker : Ksub = LinearMap.ker π := by
      ext x
      change x ∈ K ↔ π x = 0
      have hk : x ∈ K ↔
          x ∈ RingHom.ker (Ideal.Quotient.factorₐ R
            (Ideal.pow_le_pow_right n.le_succ)) := by
        rw [← hkerIdeal]
      simpa [π, RingHom.mem_ker] using hk
    have heRange : LinearMap.range e.toLinearMap = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    rw [LinearMap.exact_iff]
    symm
    calc
      LinearMap.range i = Submodule.map Ksub.subtype
          (LinearMap.range e.toLinearMap) := by rw [LinearMap.range_comp]
      _ = Submodule.map Ksub.subtype ⊤ :=
        congrArg (Submodule.map Ksub.subtype) heRange
      _ = LinearMap.range Ksub.subtype := by rw [Submodule.map_top]
      _ = Ksub := Submodule.range_subtype _
      _ = LinearMap.ker π := hker
  · intro y
    rcases Ideal.Quotient.factor_surjective
        (S := m ^ (n + 1)) (T := m ^ n)
        (Ideal.pow_le_pow_right n.le_succ) y with ⟨x, hx⟩
    exact ⟨x, by simpa [π, Ideal.Quotient.factorₐ] using hx⟩

/-- Closed-fiber injectivity propagates to every positive maximal-ideal
power quotient. -/
theorem maximalIdeal_pow_injective
    (f : N →ₗ[R] M)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    ∀ n : ℕ, 1 ≤ n →
      Function.Injective (f.quotientMapByIdeal ((maximalIdeal R) ^ n)) := by
  have hsucc : ∀ n : ℕ,
      Function.Injective (f.quotientMapByIdeal ((maximalIdeal R) ^ (n + 1))) := by
    intro n
    induction n with
    | zero =>
        rw [pow_one]
        exact hf
    | succ n ih =>
        let m : Ideal R := maximalIdeal R
        let K : Ideal (R ⧸ (m ^ (n + 2))) :=
          Ideal.map (Ideal.Quotient.mk (m ^ (n + 2))) (m ^ (n + 1))
        let Q₁ : Type u :=
          ((m ^ (n + 1) : Ideal R) ⧸
            (m • (⊤ : Submodule R (m ^ (n + 1) : Ideal R))))
        let i : Q₁ →ₗ[R] R ⧸ (m ^ (n + 2)) :=
          ((((K.restrictScalars R).subtype).comp
            (Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow m (n + 1)).toLinearMap) :
              Q₁ →ₗ[R] R ⧸ (m ^ (n + 2)))
        let π : R ⧸ (m ^ (n + 2)) →ₗ[R] R ⧸ (m ^ (n + 1)) :=
          (Ideal.Quotient.factorₐ R
            (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap
        have hrow :
            Function.Injective i ∧ Function.Exact i π ∧ Function.Surjective π := by
          simpa [m, K, Q₁, i, π, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            maximalIdeal_pow_successor_exact (R := R) (n + 1)
        rcases hrow with ⟨hi, hExact, hπ⟩
        have hQ₁ : Function.Injective (f.rTensor Q₁) :=
          rTensor_injective_of_mod_maximalIdeal_injective
            (R := R) (P := N) (P' := M) f hf Q₁
        have hQ₃ : Function.Injective (f.rTensor (R ⧸ (m ^ (n + 1)))) :=
          (LinearMap.quotientMapByIdeal_injective_iff_rTensor_injective
            (m ^ (n + 1)) f).mp ih
        have hQ₂ : Function.Injective (f.rTensor (R ⧸ (m ^ (n + 2)))) :=
          rTensor_injective_of_shortExact
            (R := R) (P := N) (Q := M) f hi hExact hπ hQ₁ hQ₃
        exact (LinearMap.quotientMapByIdeal_injective_iff_rTensor_injective
          (m ^ (n + 2)) f).mpr hQ₂
  intro n hn
  cases n with
  | zero => cases hn
  | succ k => simpa using hsucc k

omit [IsLocalRing S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
  [Module.Flat R M] [Module.Finite S N] in
/-- If all positive maximal-ideal power reductions are injective, Krull
intersection on the finite source module gives injectivity upstairs. -/
theorem injective_of_maximalIdeal_pow
    (f : N →ₗ[R] M)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      Function.Injective (f.quotientMapByIdeal ((maximalIdeal R) ^ n)))
    (hinter :
      (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) = ⊥) :
    Function.Injective f := by
  intro x y hxy
  have hmem_pow (n : ℕ) (hn : 1 ≤ n) :
      x - y ∈ ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
        (⊤ : Submodule S N)) : Submodule S N) := by
    have hxyQ :
        (Submodule.Quotient.mk (f x) :
          M ⧸ (((maximalIdeal R) ^ n) • (⊤ : Submodule R M))) =
        Submodule.Quotient.mk (f y) := by
      simpa [hxy]
    have hmk :
        (Submodule.Quotient.mk x :
          N ⧸ (((maximalIdeal R) ^ n) • (⊤ : Submodule R N))) =
        Submodule.Quotient.mk y :=
      hpow n hn <| by simpa [LinearMap.quotientMapByIdeal] using hxyQ
    have hpow_mem :
        x - y ∈ (((maximalIdeal R) ^ n) •
          (⊤ : Submodule R N) : Submodule R N) :=
      (Submodule.Quotient.eq
        (((maximalIdeal R) ^ n) • (⊤ : Submodule R N))).mp hmk
    have hmap_mem :
        x - y ∈ ((((Ideal.map (algebraMap R S) ((maximalIdeal R) ^ n)) •
          (⊤ : Submodule S N)).restrictScalars R) : Submodule R N) := by
      simpa only [Ideal.smul_restrictScalars, Submodule.restrictScalars_top] using hpow_mem
    simpa [Ideal.map_pow] using hmap_mem
  have hmem_iInf :
      x - y ∈ (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) := by
    rw [Submodule.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ k => exact hmem_pow (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hzero : x - y ∈ (⊥ : Submodule S N) := by
    simpa [hinter] using hmem_iInf
  simpa [sub_eq_zero] using hzero

include S

/-- A linear map from a finite module over a Noetherian local target to a
flat module is injective when its reduction on the closed fiber is injective. -/
@[stacks 00ME "closed-fiber injectivity criterion"]
theorem injective_of_mod_maximalIdeal_injective
    (f : N →ₗ[R] M)
    (hf : Function.Injective (f.quotientMapByIdeal (maximalIdeal R))) :
    Function.Injective f := by
  have hpow : ∀ n : ℕ, 1 ≤ n →
      Function.Injective (f.quotientMapByIdeal ((maximalIdeal R) ^ n)) :=
    maximalIdeal_pow_injective (R := R) (M := M) (N := N) f hf
  have hinter :
      (⨅ n : ℕ,
        ((((Ideal.map (algebraMap R S) (maximalIdeal R)) ^ n) •
          (⊤ : Submodule S N)) : Submodule S N)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing
      (R := S) (M := N) (I := Ideal.map (algebraMap R S) (maximalIdeal R))
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact injective_of_maximalIdeal_pow
    (R := R) (S := S) (M := M) (N := N) f hpow hinter

end LinearMap.ClosedFiber
