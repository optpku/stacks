module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective

/-!
# Flat Characterization of Finite Projective Modules

This leaf records the finite-presentation-and-flat characterization of the
canonical predicate `Module.FiniteProjective`.
-/

@[expose] public section

universe u v

namespace Module.FiniteProjective

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite projectivity implies finite presentation over a ring. -/
@[stacks 058R "finite projective modules are finitely presented"]
theorem finitePresentation (h : Module.FiniteProjective R M) :
    Module.FinitePresentation R M := by
  exact @Module.finitePresentation_of_projective R M _ _ _ h.projective h.finite

section CommRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite projective module is flat. -/
@[stacks 058R "finite projective modules are flat"]
theorem flat (h : Module.FiniteProjective R M) : Module.Flat R M := by
  exact @Module.Flat.of_projective R M _ _ _ h.projective

/-- Finite presentation and flatness construct finite projectivity. -/
@[stacks 058R "finite projective modules from finitely presented flat modules"]
theorem of_finitePresentation_of_flat
    (hfinitePresentation : Module.FinitePresentation R M) (hflat : Module.Flat R M) :
    Module.FiniteProjective R M := by
  have hfinite : Module.Finite R M := by
    rcases hfinitePresentation.out with ⟨s, hs, _⟩
    exact ⟨s, hs⟩
  exact ⟨hfinite,
    @Module.Flat.projective_of_finitePresentation R M _ _ _ hflat hfinitePresentation⟩

/-- Finite projectivity is equivalent to finite presentation and flatness. -/
@[stacks 058R "finite projective iff finitely presented flat"]
theorem iff_finitePresentation_and_flat :
    Module.FiniteProjective R M ↔ Module.FinitePresentation R M ∧ Module.Flat R M := by
  constructor
  · intro h
    exact ⟨h.finitePresentation, h.flat⟩
  · rintro ⟨hfinitePresentation, hflat⟩
    exact of_finitePresentation_of_flat hfinitePresentation hflat

end CommRing

end Module.FiniteProjective
