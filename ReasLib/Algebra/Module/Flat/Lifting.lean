/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Flat.FiniteFreeFactorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting maps from finitely presented modules to flat modules

This leaf characterizes flatness by the lifting property of maps from
finitely presented modules along surjective linear maps.

@stack 058F
-/

@[expose] public section

universe u v w x

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Maps from any finitely presented module to a flat module lift along any
surjective linear map. The test and cover universes are independent of `R` and `M`. -/
theorem postcomp_surjective_of_finitePresentation [Module.Flat R M]
    {P : Type w} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    {N : Type x} [AddCommGroup N] [Module R N]
    (π : N →ₗ[R] M) (hπ : Function.Surjective π) :
    Function.Surjective (fun f : P →ₗ[R] N ↦ π.comp f) := by
  intro f
  obtain ⟨n, a, b, hf⟩ := exists_factorization_of_finitePresentation f
  obtain ⟨g, hg⟩ := Module.projective_lifting_property π b hπ
  refine ⟨g.comp a, ?_⟩
  change π.comp (g.comp a) = f
  rw [← LinearMap.comp_assoc, hg, ← hf]

/-- Lemma 10.81.3: `M` is flat exactly when maps from finitely presented
modules to `M` lift along every surjective linear map onto `M`.

The test universe contains `R`, and the cover universe contains both `R` and `M`.
Thus the converse can test the actual free cover `M →₀ R`, lifted to the cover
universe. For arbitrary test and cover universes, use
`Module.Flat.postcomp_surjective_of_finitePresentation`. -/
@[stacks 058F]
theorem iff_postcomp_surjective_finitePresentation :
    Module.Flat R M ↔
      ∀ {P : Type (max u w)} [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P]
        {N : Type (max u v x)} [AddCommGroup N] [Module R N]
        (π : N →ₗ[R] M), Function.Surjective π →
          Function.Surjective (fun f : P →ₗ[R] N ↦ π.comp f) := by
  constructor
  · intro hM P _ _ _ N _ _ π hπ
    letI : Module.Flat R M := hM
    exact postcomp_surjective_of_finitePresentation π hπ
  · intro H
    apply (iff_finiteFree_factorization.{u, v, w}).2
    intro P _ _ _ f
    let e : ULift.{x} (M →₀ R) ≃ₗ[R] (M →₀ R) := ULift.moduleEquiv
    let π : ULift.{x} (M →₀ R) →ₗ[R] M :=
      (Finsupp.linearCombination R (id : M → M)).comp e.toLinearMap
    have hπ : Function.Surjective π :=
      (Finsupp.linearCombination_id_surjective R M).comp e.surjective
    obtain ⟨g, hg⟩ := H π hπ f
    change π.comp g = f at hg
    -- The lifted free cover is flat. Factor the lift using the already proved
    -- arbitrary-universe forward lemma, then compose with the cover map.
    obtain ⟨n, a, b, hab⟩ := exists_factorization_of_finitePresentation g
    refine ⟨n, a, π.comp b, ?_⟩
    rw [LinearMap.comp_assoc, ← hab, hg]

end Module.Flat
