module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective modules are flat

@stack 058R

Mathlib registers this fact as a canonical instance. This leaf supplies the explicit companion
for APIs that consume a projectivity proof as data and should not install a local instance.
-/

@[expose] public section

universe u v

namespace Module.Projective

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- Explicit-hypothesis form of the canonical flatness instance for projective modules. -/
@[stacks 058R "projective modules are flat"]
theorem flat (hM : Module.Projective R M) : Module.Flat R M := sorry

end Module.Projective

namespace Module.FinitePresentation

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-! Finitely presented flat modules are projective. -/

/-- A finitely presented flat module over a commutative ring is projective. -/
theorem projective_of_flat
    (hfinitePresentation : Module.FinitePresentation A M) (hflat : Module.Flat A M) :
    Module.Projective A M := sorry

end Module.FinitePresentation

namespace Module

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

/-- A finite flat module that is not projective forces its coefficient ring to be non-Noetherian. -/
theorem not_isNoetherianRing_of_finite_flat_not_projective
    [Module.Finite A M] [Module.Flat A M] (h : ¬ Module.Projective A M) :
    ¬ IsNoetherianRing A := sorry

end Module
