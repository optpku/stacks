module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite Presentation and Restriction of Scalars

This file records finite presentation for a compatible module under change of scalars. Finite-type
scalar extension gives the forward direction. If the scalar algebra is finitely presented as a
module, finite presentation is equivalent before and after restriction of scalars.
-/

@[expose] public section

universe u v w

namespace Module.FinitePresentation

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- A module finitely presented after restricting scalars to `R` is finitely presented over a
finite-type `R`-algebra `S`. -/
@[stacks 0561]
theorem of_restrictScalars [Algebra.FiniteType R S] [Module.FinitePresentation R M] :
    Module.FinitePresentation S M := sorry

/-- Finite presentation over `R` and `S` is equivalent when `S` is finitely presented as an
`R`-module. -/
@[stacks 0564 "module finite presentation"]
theorem iff_restrictScalars [Module.FinitePresentation R S] :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := sorry

/-- Finite presentation is unchanged by restriction of scalars along a finite, finitely
presented algebra. -/
@[stacks 0564]
theorem iff_restrictScalars_of_finite [Module.Finite R S] [Algebra.FinitePresentation R S] :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := sorry

end Module.FinitePresentation
