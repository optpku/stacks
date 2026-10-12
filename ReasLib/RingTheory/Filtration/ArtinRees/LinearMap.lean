/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artin-Rees Bounds for Linear Maps

@stack 00IO

This file packages the Artin-Rees lemma in a form adapted to linear maps.  The owner-level
statement controls inverse images of adic powers; exact sequences then identify the kernel term
with the prescribed submodule.
-/

@[expose] public section

open scoped Pointwise

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap

/-- An Artin-Rees bound for a linear map `f` with respect to an ideal `I`. -/
@[stacks 00IO "Artin-Rees bound for a linear map"]
def IsArtinReesBound (f : M →ₗ[R] N) (I : Ideal R) (c : ℕ) : Prop :=
  ∀ n ≥ c, f.range ⊓ I ^ n • ⊤ ≤ Submodule.map f (I ^ (n - c) • ⊤)

/-- An Artin-Rees formula for inverse images supplies an Artin-Rees bound for the map. -/
theorem isArtinReesBound_of_preimage_pow_smul_eq (I : Ideal R) {f : M →ₗ[R] N} {c : ℕ}
    (hc : ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) :
    f.IsArtinReesBound I c := by
  intro n hn y hy
  obtain ⟨x, rfl⟩ := hy.1
  have hx : x ∈ Submodule.comap f (I ^ n • ⊤) := hy.2
  rw [hc n hn] at hx
  obtain ⟨k, hk, z, hz, hkz⟩ := Submodule.mem_sup.mp hx
  have hz' : z ∈ I ^ (n - c) • (⊤ : Submodule R M) := by
    exact (smul_mono_right (I ^ (n - c)) le_top :
      I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) ≤ I ^ (n - c) • ⊤) hz
  refine Submodule.mem_map.mpr ⟨z, hz', ?_⟩
  rw [← hkz, map_add, hk, zero_add]

end LinearMap

namespace Ideal

/-- A linear map into a finite module over a Noetherian ring admits a uniform Artin-Rees
formula for inverse images of powers of an ideal. -/
@[stacks 00IO "inverse-image Artin-Rees formula"]
theorem exists_exact_preimage_pow_smul_eq [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) := by
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨c, fun n hn ↦ ?_⟩
  calc
    Submodule.comap f (I ^ n • ⊤) =
        Submodule.comap f (I ^ n • ⊤ ⊓ LinearMap.range f) := by
      ext x
      simp only [Submodule.mem_comap, Submodule.mem_inf]
      constructor
      · intro hx
        exact ⟨hx, ⟨x, rfl⟩⟩
      · exact fun hx ↦ hx.1
    _ = Submodule.comap f
        (I ^ (n - c) • (I ^ c • ⊤ ⊓ LinearMap.range f)) := by
      rw [hc n hn]
    _ = Submodule.comap f
        (I ^ (n - c) • Submodule.map f (Submodule.comap f (I ^ c • ⊤))) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = Submodule.comap f
        (Submodule.map f (I ^ (n - c) • Submodule.comap f (I ^ c • ⊤))) := by
      rw [Submodule.map_smul'']
    _ = I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) ⊔ LinearMap.ker f := by
      rw [Submodule.comap_map_eq]
    _ = LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) := sup_comm _ _

/-- Lemma 10.51.3, tag `00IO`: an exact sequence into a finite module over a Noetherian ring
admits one Artin-Rees constant controlling both inverse images and image intersections. -/
@[stacks 00IO]
theorem exists_artin_rees_constant_of_exact [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) {K : Submodule R M} {f : M →ₗ[R] N}
    (h_exact : Function.Exact K.subtype f) :
    ∃ c : ℕ,
      (∀ n ≥ c,
        Submodule.comap f (I ^ n • ⊤) = K ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) ∧
        f.IsArtinReesBound I c := by
  obtain ⟨c, hc⟩ := I.exists_exact_preimage_pow_smul_eq f
  refine ⟨c, ?_, LinearMap.isArtinReesBound_of_preimage_pow_smul_eq I hc⟩
  intro n hn
  rw [hc n hn, h_exact.linearMap_ker_eq, Submodule.range_subtype]

end Ideal
