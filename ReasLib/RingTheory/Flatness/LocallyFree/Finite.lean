/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective.Flat
public import ReasLib.RingTheory.Flatness.LocallyFree

/-!
# Finite Locally Free Modules

This leaf owns the atomic consequences, constructions, and characterizations
of `Module.FiniteLocallyFree`, including its relationships with finite
projective modules, flatness, and the free locus.
-/

@[expose] public section

universe u v

namespace Module

namespace FiniteLocallyFree

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite locally free module is finite. -/
@[stacks 00NX "finite locally free modules are finite"]
theorem finite (h : FiniteLocallyFree R M) : Module.Finite R M := by
  obtain ⟨s, hs, hlocal⟩ := h.exists_standardOpen_cover
  exact Module.Finite.of_localizationSpan s hs fun g ↦ (hlocal g g.property).2

/-- Finite local freeness supplies finite generation to typeclass search. -/
instance instFinite [h : FiniteLocallyFree R M] : Module.Finite R M := h.finite

/-- A finite locally free module is finitely presented. -/
@[stacks 00NX "finite locally free modules are finitely presented"]
theorem finitePresentation (h : FiniteLocallyFree R M) : Module.FinitePresentation R M := by
  obtain ⟨s, hs, hlocal⟩ := h.exists_standardOpen_cover
  refine Module.FinitePresentation.of_localizationSpan s hs fun g ↦ ?_
  letI := (hlocal g g.property).1
  letI := (hlocal g g.property).2
  exact Module.finitePresentation_of_projective _ _

/-- Finite local freeness supplies finite presentation to typeclass search. -/
instance instFinitePresentation [h : FiniteLocallyFree R M] :
    Module.FinitePresentation R M := h.finitePresentation

/-- The free locus of a finite locally free module is all of `Spec R`. -/
@[stacks 00NX "free locus of a finite locally free module"]
theorem freeLocus_eq_univ (h : FiniteLocallyFree R M) :
    freeLocus R M = Set.univ := sorry

/-- A finite locally free module is projective. -/
@[stacks 00NX "finite locally free modules are projective"]
theorem projective (h : FiniteLocallyFree R M) : Projective R M := by
  letI := h.finitePresentation
  have hflat : Flat R M := by
    obtain ⟨s, hs, hlocal⟩ := h.exists_standardOpen_cover
    refine Module.flat_of_localized_span R M s hs fun g ↦ ?_
    letI := (hlocal g g.property).1
    exact (Module.flat_iff_of_isLocalization (Localization.Away g.val)
      (Submonoid.powers g.val) (LocalizedModule.Away g.val M)).mp inferInstance
  exact @Module.Flat.projective_of_finitePresentation R M _ _ _ hflat inferInstance

/-- Finite local freeness supplies projectivity to typeclass search. -/
instance instProjective [h : FiniteLocallyFree R M] : Projective R M := h.projective

/-- A finite locally free module is flat. -/
@[stacks 00NX "finite locally free modules are flat"]
theorem flat (h : FiniteLocallyFree R M) : Flat R M :=
  @Module.Flat.of_projective R M _ _ _ h.projective

/-- Finite generation and local freeness construct finite local freeness. -/
@[stacks 00NX "finite locally free module from finite locally free data"]
theorem of_finite_and_locallyFree
    (hfinite : Module.Finite R M) (hlocallyFree : LocallyFree R M) :
    FiniteLocallyFree R M := sorry

/-- Finite presentation and an everywhere-free stalk locus construct finite local
freeness. -/
@[stacks 00NX "finite locally free module from its free locus"]
theorem of_finitePresentation_of_freeLocus_eq_univ
    (hfinitePresentation : Module.FinitePresentation R M)
    (hfree : freeLocus R M = Set.univ) :
    FiniteLocallyFree R M := sorry

/-- A finitely presented flat module is finite locally free. -/
@[stacks 00NX "finitely presented flat modules are finite locally free"]
theorem of_finitePresentation_of_flat
    (hfinitePresentation : Module.FinitePresentation R M) (hflat : Flat R M) :
    FiniteLocallyFree R M := sorry

/-- Finite local freeness is equivalent to finite presentation and flatness. -/
@[stacks 00NX "finite locally free iff finitely presented flat"]
theorem iff_finitePresentation_and_flat :
    FiniteLocallyFree R M ↔ Module.FinitePresentation R M ∧ Flat R M := sorry

/-- Finite local freeness is equivalent to the canonical finite-projective
predicate. -/
@[stacks 00NX "finite locally free iff finite projective"]
theorem iff_finiteProjective :
    FiniteLocallyFree R M ↔ Module.FiniteProjective R M := sorry

/-- Finite local freeness is equivalent to finite generation together with local
freeness. -/
@[stacks 00NX "finite locally free iff finite locally free data"]
theorem iff_finite_and_locallyFree :
    FiniteLocallyFree R M ↔ Module.Finite R M ∧ LocallyFree R M := sorry

/-- Finite local freeness is equivalent to finite presentation and an everywhere-free
stalk locus. -/
@[stacks 00NX "finite locally free iff finitely presented with free locus"]
theorem iff_finitePresentation_and_freeLocus_eq_univ :
    FiniteLocallyFree R M ↔
      Module.FinitePresentation R M ∧ freeLocus R M = Set.univ := sorry

end FiniteLocallyFree

end Module
