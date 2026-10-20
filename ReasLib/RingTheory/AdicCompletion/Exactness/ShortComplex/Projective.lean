/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective.Flat
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex.Flat

/-!
# Sections of completed surjections with projective reduction

@stack 05D3

The short-complex splitting theorem and this map-level section theorem share
the same completion context but have different reusable interfaces.  Keeping
the section as its own owner lets projective-descent consumers use a linear map
without constructing a `ShortComplex` package.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Lemma 10.97.9 (05D3): a surjection onto a flat module whose reduction
modulo `I` is projective admits a section after `I`-adic completion.  The
section is explicit data; only the existence proof is deferred. -/
@[stacks 05D3 "section of a completed flat surjection with projective quotient"]
theorem map_has_section_of_flat_of_projective_quotient
    (g : P →ₗ[R] M) [Module.Flat R M] (hg : Function.Surjective g)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    ∃ s : AdicCompletion I M →ₗ[AdicCompletion I R] AdicCompletion I P,
      (AdicCompletion.map I g).comp s = LinearMap.id := sorry

/-- Lemma 10.97.9 (05D3): completing a short exact sequence with flat
cokernel and projective closed fiber yields a split short complex. -/
@[stacks 05D3 "splitting of a completed short exact sequence"]
theorem mapShortComplex_splitting_of_flat_of_projective_quotient
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) [Module.Flat R S.X₃]
    (hquot : Module.Projective (R ⧸ I) (S.X₃ ⧸ (I • ⊤ : Submodule R S.X₃))) :
    Nonempty (mapShortComplex I S).Splitting := by
  have hcompleted := mapShortComplex_shortExact_of_flat I hS
  have hg : Function.Surjective S.g.hom :=
    (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  obtain ⟨s, hs⟩ :=
    map_has_section_of_flat_of_projective_quotient I S.g.hom hg hquot
  refine ⟨ShortComplex.Splitting.ofExactOfSection
    (mapShortComplex I S) hcompleted.exact (ModuleCat.ofHom s) ?_ hcompleted.mono_f⟩
  ext x
  exact LinearMap.congr_fun hs x

end AdicCompletion
