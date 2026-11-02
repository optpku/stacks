/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Module.ULift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free factorization criterion for flat modules

@stack 058E
-/

@[expose] public section

universe u v w

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.81.2: `M` is flat exactly when every map from a finitely
presented module to `M` factors through a finite-free module.

The test universe contains `R`: the converse uses the finitely presented quotient
of `Fin l →₀ R` by one relation, transported by `ULift` to `Type (max u w)`.
The forward implication for test modules in an arbitrary universe is
`Module.Flat.exists_factorization_of_finitePresentation`. -/
@[stacks 058E]
theorem iff_finiteFree_factorization :
    Module.Flat R M ↔
      ∀ {P : Type (max u w)} [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P] (f : P →ₗ[R] M),
        ∃ (n : ℕ) (h : P →ₗ[R] (Fin n →₀ R))
          (g : (Fin n →₀ R) →ₗ[R] M), f = g.comp h := by
  constructor
  · intro hM P _ _ _ f
    letI : Module.Flat R M := hM
    exact exists_factorization_of_finitePresentation f
  · intro H
    apply of_forall_exists_factorization
    intro l a f hfa
    let K : Submodule R (Fin l →₀ R) := Submodule.span R {a}
    have hK : K.FG := Submodule.fg_span_singleton a
    letI : Module.FinitePresentation R ((Fin l →₀ R) ⧸ K) :=
      Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective
        (by simpa using hK)
    let e : ULift.{w} ((Fin l →₀ R) ⧸ K) ≃ₗ[R] ((Fin l →₀ R) ⧸ K) :=
      ULift.moduleEquiv
    letI : Module.FinitePresentation R (ULift.{w} ((Fin l →₀ R) ⧸ K)) :=
      Module.FinitePresentation.of_equiv e.symm
    have hker : K ≤ LinearMap.ker f :=
      (Submodule.span_singleton_le_iff_mem a (LinearMap.ker f)).2 hfa
    let fbar : ((Fin l →₀ R) ⧸ K) →ₗ[R] M := K.liftQ f hker
    obtain ⟨n, h, g, hh⟩ := H (fbar.comp e.toLinearMap)
    refine ⟨n, (h.comp e.symm.toLinearMap).comp K.mkQ, g, ?_, ?_⟩
    · apply LinearMap.ext
      intro z
      have hz := LinearMap.congr_fun hh (e.symm (K.mkQ z))
      simpa [fbar] using hz
    · have ha : K.mkQ a = 0 := by
        apply (Submodule.Quotient.mk_eq_zero K).mpr
        exact Submodule.subset_span (Set.mem_singleton a)
      simp only [LinearMap.comp_apply, ha, map_zero]

end Module.Flat
