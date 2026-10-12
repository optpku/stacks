/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps on submodule quotients

This leaf records general surjectivity and injectivity criteria for `Submodule.mapQ`, together with
the specialization to quotients by stabilized power kernels of an endomorphism.  These statements
are independent of ideal quotients, gradings, and Noetherian arguments, so they are owned at the
general submodule-quotient layer.
-/

@[expose] public section

universe u v w x

namespace Submodule

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {R' : Type w} [Ring R']
variable {M' : Type x} [AddCommGroup M'] [Module R' M']
variable {σ : R →+* R'}

/-- A surjective semilinear map induces a surjective map on any compatible pair of submodule
quotients. -/
@[stacks 00DV "surjectivity of induced quotient maps"]
theorem mapQ_surjective_of_surjective
    (f : M →ₛₗ[σ] M') (hf : Function.Surjective f)
    (p : Submodule R M) (q : Submodule R' M')
    (hpq : p ≤ comap f q) :
    Function.Surjective (p.mapQ q f hpq) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

end Submodule

namespace Submodule

variable {R : Type u} [Ring R]
variable {R' : Type v} [Ring R']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {M' : Type x} [AddCommGroup M'] [Module R' M']
variable {σ : R →+* R'}

/-- An induced map on submodule quotients is injective exactly when its target submodule has no
additional preimage outside the source submodule. -/
@[stacks 00DV "injectivity of induced quotient maps"]
theorem mapQ_injective_iff
    (p : Submodule R M) (q : Submodule R' M')
    (f : M →ₛₗ[σ] M') (hpq : p ≤ comap f q) :
    Function.Injective (p.mapQ q f hpq) ↔ comap f q ≤ p := by
  rw [← LinearMap.ker_eq_bot, ker_mapQ, eq_bot_iff, map_le_iff_le_comap,
    comap_bot, ker_mkQ]

/-- An induced map on submodule quotients is injective when the source submodule is the full
preimage of the target submodule. -/
@[stacks 00DV "injectivity of induced quotient maps"]
theorem mapQ_injective_of_comap_le
    (p : Submodule R M) (q : Submodule R' M')
    (f : M →ₛₗ[σ] M') (hpq : p ≤ comap f q) (hqp : comap f q ≤ p) :
    Function.Injective (p.mapQ q f hpq) :=
  (mapQ_injective_iff p q f hpq).2 hqp

end Submodule

namespace LinearMap

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The kernel of every power of an endomorphism is preserved by that endomorphism. -/
@[stacks 00K1 "endomorphism power-kernel invariance"]
theorem ker_pow_le_comap (f : M →ₗ[R] M) (r : ℕ) :
    ker (f ^ r) ≤ (ker (f ^ r)).comap f := by
  intro x hx
  change (f ^ r) (f x) = 0
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hx, map_zero]

/-- The next power kernel is exactly the preimage of the current power kernel. -/
@[stacks 00K1 "successive power-kernel comap identity"]
theorem ker_pow_succ_eq_comap (f : M →ₗ[R] M) (r : ℕ) :
    ker (f ^ (r + 1)) = (ker (f ^ r)).comap f := by
  ext x
  change (f ^ (r + 1)) x = 0 ↔ (f ^ r) (f x) = 0
  rw [Module.End.iterate_succ]
  rfl

end LinearMap

namespace LinearMap

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The map induced by an endomorphism on its `r`-th power-kernel quotient is injective exactly
when the next power kernel has already stabilized. -/
@[stacks 00K1 "power-kernel quotient injectivity criterion"]
theorem mapQ_ker_pow_injective_iff (f : M →ₗ[R] M) (r : ℕ) :
    Function.Injective
        ((ker (f ^ r)).mapQ (ker (f ^ r)) f (ker_pow_le_comap f r)) ↔
      ker (f ^ (r + 1)) ≤ ker (f ^ r) := by
  rw [Submodule.mapQ_injective_iff, ← ker_pow_succ_eq_comap]

/-- The endomorphism induced on its `r`-th power-kernel quotient is injective exactly when the
successive power kernels are equal.  This is the symmetric stabilization companion to the
minimal reverse-inclusion criterion `mapQ_ker_pow_injective_iff`. -/
@[stacks 00K1 "power-kernel quotient injectivity as stabilization"]
theorem mapQ_ker_pow_injective_iff_eq (f : M →ₗ[R] M) (r : ℕ) :
    Function.Injective
        ((ker (f ^ r)).mapQ (ker (f ^ r)) f (ker_pow_le_comap f r)) ↔
      ker (f ^ (r + 1)) = ker (f ^ r) := by
  rw [mapQ_ker_pow_injective_iff]
  constructor
  · intro h
    apply le_antisymm h
    intro x hx
    exact Module.End.pow_map_zero_of_le (Nat.le_succ r) hx
  · exact fun h ↦ h.le

/-- Stabilization of the full power-kernel filtration makes the endomorphism induced on the
stabilized quotient injective. -/
@[stacks 00K1 "stable power-kernel quotient injectivity"]
theorem mapQ_ker_pow_injective_of_iSup_eq (f : M →ₗ[R] M) {r : ℕ}
    (hstab : (⨆ m, ker (f ^ m)) = ker (f ^ r)) :
    Function.Injective
      ((ker (f ^ r)).mapQ (ker (f ^ r)) f (ker_pow_le_comap f r)) := by
  rw [mapQ_ker_pow_injective_iff, ← hstab]
  exact le_iSup (fun m ↦ ker (f ^ m)) (r + 1)

end LinearMap
