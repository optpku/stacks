module

public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completeness of submodule quotients

@stack 031A
-/

@[expose] public section

universe u v w

open AdicCompletion

namespace IsPrecomplete

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A surjective linear image of an adically precomplete module is precomplete. -/
@[stacks 031A "precompleteness descends along surjective linear maps"]
theorem of_surjective (I : Ideal R) (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] :
    IsPrecomplete I N := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I hf y
  obtain ⟨m, rfl⟩ := AdicCompletion.of_surjective I M x
  exact ⟨f m, by rw [AdicCompletion.map_of]⟩

/-- A quotient of an adically precomplete module is precomplete. -/
@[stacks 031A "precompleteness of submodule quotients"]
instance quotient (I : Ideal R) (K : Submodule R M) [IsPrecomplete I M] :
    IsPrecomplete I (M ⧸ K) :=
  of_surjective I (Submodule.mkQ K) (Submodule.mkQ_surjective K)

end IsPrecomplete

namespace Submodule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The quotient by `K` is `I`-adically Hausdorff exactly when `K` is closed for the
`I`-adic filtration. -/
@[stacks 031A "Hausdorff criterion for a submodule quotient"]
theorem isHausdorff_quotient_iff (K : Submodule R M) (I : Ideal R) :
    IsHausdorff I (M ⧸ K) ↔
      K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) := by
  have hcomap_pow (n : ℕ) :
      Submodule.comap (Submodule.mkQ K) (I ^ n • (⊤ : Submodule R (M ⧸ K))) =
        K ⊔ I ^ n • (⊤ : Submodule R M) := by
    simpa [Submodule.ker_mkQ, sup_comm] using
      Submodule.comap_smul_top_of_surjective (I ^ n) (Submodule.mkQ K)
        (Submodule.mkQ_surjective K)
  constructor
  · intro hhaus
    have hbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (M ⧸ K))) = ⊥ :=
      IsHausdorff.iInf_pow_smul hhaus
    have hcomap := congrArg (Submodule.comap (Submodule.mkQ K)) hbot
    rw [Submodule.comap_iInf] at hcomap
    simp only [Submodule.comap_bot, Submodule.ker_mkQ] at hcomap
    simpa [hcomap_pow] using hcomap.symm
  · intro hK
    rw [isHausdorff_iff]
    rintro ⟨m⟩ hm
    have hm_mem : ∀ n : ℕ, Submodule.mkQ K m ∈ I ^ n • (⊤ : Submodule R (M ⧸ K)) :=
      fun n ↦ SModEq.zero.1 (hm n)
    have hm' : m ∈ ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [← hcomap_pow n, Submodule.mem_comap]
      exact hm_mem n
    have hmK : m ∈ K := by
      rw [hK]
      exact hm'
    change (Submodule.Quotient.mk m : M ⧸ K) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmK

/-- If `M` is `I`-adically precomplete, its quotient by `K` is complete exactly when `K` is
closed for the `I`-adic filtration. -/
@[stacks 031A "adic completeness criterion for a submodule quotient"]
theorem isAdicComplete_quotient_iff (K : Submodule R M) (I : Ideal R)
    [IsPrecomplete I M] :
    IsAdicComplete I (M ⧸ K) ↔
      K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) := by
  constructor
  · intro h
    exact (K.isHausdorff_quotient_iff I).mp h.toIsHausdorff
  · intro h
    rw [isAdicComplete_iff]
    exact ⟨(K.isHausdorff_quotient_iff I).mpr h, inferInstance⟩

end Submodule
