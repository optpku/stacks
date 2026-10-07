module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
theorem finite (h : FiniteLocallyFree R M) : Module.Finite R M := sorry

/-- Finite local freeness supplies finite generation to typeclass search. -/
instance instFinite [FiniteLocallyFree R M] : Module.Finite R M := sorry

/-- A finite locally free module is finitely presented. -/
@[stacks 00NX "finite locally free modules are finitely presented"]
theorem finitePresentation (h : FiniteLocallyFree R M) : Module.FinitePresentation R M := sorry

/-- Finite local freeness supplies finite presentation to typeclass search. -/
instance instFinitePresentation [FiniteLocallyFree R M] : Module.FinitePresentation R M := sorry

/-- The free locus of a finite locally free module is all of `Spec R`. -/
@[stacks 00NX "free locus of a finite locally free module"]
theorem freeLocus_eq_univ (h : FiniteLocallyFree R M) :
    freeLocus R M = Set.univ := sorry

/-- A finite locally free module is projective. -/
@[stacks 00NX "finite locally free modules are projective"]
theorem projective (h : FiniteLocallyFree R M) : Projective R M := sorry

/-- Finite local freeness supplies projectivity to typeclass search. -/
instance instProjective [FiniteLocallyFree R M] : Projective R M := sorry

/-- A finite locally free module is flat. -/
@[stacks 00NX "finite locally free modules are flat"]
theorem flat (h : FiniteLocallyFree R M) : Flat R M := sorry

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
