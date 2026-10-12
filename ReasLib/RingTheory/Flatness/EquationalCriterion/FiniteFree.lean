/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.TFAE

/-!
# Finite-Free Equational Criteria for Flatness

This file packages the equational criterion using maps from finite powers `Fin n → R` and
factorizations through finite free `Finsupp` modules.

@stack 058D
-/

@[expose] public section

universe u v

open LinearMap

namespace Module.Flat.FiniteFree

/-- Every kernel element can be killed by a factorization through a finite free module. -/
@[stacks 058D "finite-free kernel factorization"]
def KernelFactorization (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (x : Fin n → R),
    f x = 0 →
      ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R))
        (g : (Fin m →₀ R) →ₗ[R] M),
        f = g ∘ₗ h ∧ h x = 0

/-- A factorization killing `N` can be refined to kill one more kernel element. -/
@[stacks 058D "finite-free kernel-factorization refinement"]
def KernelRefinement (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃n m : ℕ⦄ (f : (Fin n → R) →ₗ[R] M)
    (N : Submodule R (Fin n → R))
    (h : (Fin n → R) →ₗ[R] (Fin m →₀ R)),
    N ≤ ker f →
      N ≤ ker h →
        (∃ g : (Fin m →₀ R) →ₗ[R] M, f = g ∘ₗ h) →
          ∀ x : Fin n → R,
            f x = 0 →
              ∃ (m' : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m' →₀ R)),
                N + Submodule.span R ({x} : Set (Fin n → R)) ≤ ker h' ∧
                  ∃ g' : (Fin m' →₀ R) →ₗ[R] M, f = g' ∘ₗ h'

/-- Every finitely generated submodule of a kernel can be killed by a finite-free factorization. -/
@[stacks 058D "finitely generated kernel factorization"]
def FGKernelFactorization (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M)
    (N : Submodule R (Fin n → R)),
    N ≤ ker f →
      N.FG →
        ∃ (m : ℕ) (h : (Fin n → R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h ∧ N ≤ ker h

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Transport the function-model kernel criterion to Mathlib's `Finsupp` model. -/
theorem KernelFactorization.toFinsupp (h : KernelFactorization R M) :
    ∀ ⦃n : ℕ⦄ (f : (Fin n →₀ R) →ₗ[R] M) (x : Fin n →₀ R),
      f x = 0 →
        ∃ (m : ℕ) (h' : (Fin n →₀ R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ h' x = 0 := by
  intro n f x hx
  let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R :=
    Finsupp.linearEquivFunOnFinite R R (Fin n)
  obtain ⟨m, h', g, hfactor, hx'⟩ :=
    h (f ∘ₗ e.symm.toLinearMap) (e x) (by simpa [e] using hx)
  refine ⟨m, h' ∘ₗ e.toLinearMap, g, ?_, ?_⟩
  · simpa [LinearMap.comp_assoc] using
      congrArg (fun phi => phi ∘ₗ e.toLinearMap) hfactor
  · simpa [e] using hx'

/-- The function-model kernel criterion implies flatness. -/
theorem KernelFactorization.flat (h : KernelFactorization R M) :
    Module.Flat R M := by
  have hFinsupp := h.toFinsupp
  exact Module.Flat.of_forall_exists_factorization fun {l} {f} {x} hx =>
    hFinsupp x f hx

/-- Flatness is equivalent to the finite-free kernel factorization criterion. -/
@[stacks 058D "flatness via finite-free kernel factorization"]
theorem flat_iff_kernelFactorization :
    Module.Flat R M ↔ KernelFactorization R M := by
  constructor
  · intro hflat
    letI : Module.Flat R M := hflat
    intro n f x hx
    simpa using
      (Module.Flat.exists_factorization_of_apply_eq_zero_of_free
        (R := R) (M := M) (N := Fin n → R) (f := x) (x := f) hx)
  · exact KernelFactorization.flat

/-- Iterating one-element refinements kills the span of a finite set of kernel elements. -/
theorem KernelRefinement.exists_factorization_killing_span_finset
    (h : KernelRefinement R M) :
    ∀ ⦃n : ℕ⦄ (f : (Fin n → R) →ₗ[R] M) (s : Finset (Fin n → R)),
      (∀ x ∈ s, f x = 0) →
        ∃ (m : ℕ) (h' : (Fin n → R) →ₗ[R] (Fin m →₀ R))
          (g : (Fin m →₀ R) →ₗ[R] M),
          f = g ∘ₗ h' ∧ Submodule.span R (s : Set (Fin n → R)) ≤ ker h' := by
  classical
  intro n f s hs
  induction s using Finset.induction with
  | empty =>
      let e : (Fin n →₀ R) ≃ₗ[R] Fin n → R :=
        Finsupp.linearEquivFunOnFinite R R (Fin n)
      refine ⟨n, e.symm.toLinearMap, f ∘ₗ e.toLinearMap, ?_, ?_⟩
      · ext x
        simp [e]
      · simp
  | insert x s hx_not_mem ih =>
      have hs_tail : ∀ y ∈ s, f y = 0 := by
        intro y hy
        exact hs y (Finset.mem_insert_of_mem hy)
      obtain ⟨m, h', g, hfactor, hkill⟩ := ih hs_tail
      have hspan_ker_f : Submodule.span R (s : Set (Fin n → R)) ≤ ker f := by
        rw [hfactor]
        exact hkill.trans (LinearMap.ker_le_ker_comp h' g)
      have hx_zero : f x = 0 := hs x (Finset.mem_insert_self x s)
      obtain ⟨m', h'', hsup, g', hfactor'⟩ :=
        h f (Submodule.span R (s : Set (Fin n → R))) h'
          hspan_ker_f hkill ⟨g, hfactor⟩ x hx_zero
      refine ⟨m', h'', g', hfactor', ?_⟩
      rw [Finset.coe_insert, Submodule.span_insert]
      simpa [Submodule.add_eq_sup, sup_comm] using hsup

/-- The four finite-free formulations of the equational criterion are equivalent. -/
@[stacks 058D "finite-free equational criterion"]
theorem tfae :
    List.TFAE
      [ Module.Flat R M,
        KernelFactorization R M,
        KernelRefinement R M,
        FGKernelFactorization R M ] := by
  tfae_have 1 ↔ 2 := by
    exact flat_iff_kernelFactorization
  tfae_have 2 → 3 := by
    intro h n m f N h' hNkerf hNkerh hfactor x hx
    have hFinsupp := h.toFinsupp
    obtain ⟨g, hg⟩ := hfactor
    obtain ⟨m', h'', g', hg', hhx⟩ :=
      hFinsupp g (h' x) (by simpa [hg, LinearMap.comp_apply] using hx)
    refine ⟨m', h'' ∘ₗ h', ?_, g', ?_⟩
    · rw [Submodule.add_eq_sup]
      refine sup_le ?_ ?_
      · exact hNkerh.trans (LinearMap.ker_le_ker_comp h' h'')
      · have hxker : x ∈ ker (h'' ∘ₗ h') := by
          simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hhx
        refine Submodule.span_le.2 ?_
        intro y hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact hxker
    · calc
        f = g ∘ₗ h' := hg
        _ = (g' ∘ₗ h'') ∘ₗ h' := by rw [hg']
        _ = g' ∘ₗ (h'' ∘ₗ h') := by rw [LinearMap.comp_assoc]
  tfae_have 3 → 4 := by
    intro h n f N hNkerf hNfg
    classical
    obtain ⟨S, hSfinite, hSspan⟩ := Submodule.fg_def.mp hNfg
    let s : Finset (Fin n → R) := hSfinite.toFinset
    have hs_span : Submodule.span R (s : Set (Fin n → R)) = N := by
      simpa [s] using hSspan
    have hs_zero : ∀ x ∈ s, f x = 0 := by
      intro x hx
      have hxN : x ∈ N := by
        rw [← hs_span]
        exact Submodule.subset_span hx
      simpa [LinearMap.mem_ker] using hNkerf hxN
    obtain ⟨m, h', g, hfactor, hkill⟩ :=
      h.exists_factorization_killing_span_finset f s hs_zero
    refine ⟨m, h', g, hfactor, ?_⟩
    rw [← hs_span]
    exact hkill
  tfae_have 4 → 2 := by
    intro h n f x hx
    have hxspan : Submodule.span R ({x} : Set (Fin n → R)) ≤ ker f := by
      refine Submodule.span_le.2 ?_
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      simpa [LinearMap.mem_ker] using hx
    have hfg : (Submodule.span R ({x} : Set (Fin n → R))).FG := by
      simpa using (Submodule.fg_span_singleton (R := R) x)
    obtain ⟨m, h', g, hfactor, hkill⟩ :=
      h f (Submodule.span R ({x} : Set (Fin n → R))) hxspan hfg
    refine ⟨m, h', g, hfactor, ?_⟩
    have hxker : x ∈ ker h' := hkill (Submodule.subset_span (by simp))
    simpa [LinearMap.mem_ker] using hxker
  tfae_finish

/-- Flatness is equivalent to the one-element refinement criterion. -/
@[stacks 058D "flatness via finite-free kernel refinement"]
theorem flat_iff_kernelRefinement :
    Module.Flat R M ↔ KernelRefinement R M :=
  tfae.out 0 2

/-- Flatness is equivalent to killing finitely generated kernel submodules. -/
@[stacks 058D "flatness via finitely generated kernel factorization"]
theorem flat_iff_fgKernelFactorization :
    Module.Flat R M ↔ FGKernelFactorization R M :=
  tfae.out 0 3

end Module.Flat.FiniteFree
