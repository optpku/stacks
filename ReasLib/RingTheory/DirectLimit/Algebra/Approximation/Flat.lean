module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Flat
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Specialization
public import ReasLib.Algebra.Module.Flat.Relative
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness in directed finite-module approximations

This leaf contains the flatness consequences of a directed finite-module
approximation.  The source-faithful arbitrary-system result is owned by
`Approximation.ModuleSystem.Flat`; this leaf only specializes it along
`Module.toSystem`.
-/

@[expose] public section

universe u v w x

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Module

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Flatness of the limiting module over the limiting source descends to one
stage of a finite-type finite-module approximation.  The finite-presentation
hypotheses of the source theorem follow from `A.toSystem` and its
`hasFinitePresentation` specialization; the source-faithful arbitrary-system
theorem is `ModuleSystem.exists_flat_stage`. -/
@[stacks 00R1 "flatness in a finite-type approximation"]
theorem exists_flat_stage (A : Module f M)
    (hflat : _root_.Module.FlatAlong f M) :
    ∃ i : A.index,
      _root_.Module.FlatAlong (A.map i) (A.moduleStage i) := sorry

/-- Flatness of a stage module over its source stage persists along every
later transition of a finite-type finite-module approximation. -/
@[stacks 00R1 "flatness in a finite-type approximation"]
theorem flat_later (A : Module f M) {i j : A.index} (hij : i ≤ j)
    (hflat : _root_.Module.FlatAlong (A.map i) (A.moduleStage i)) :
    _root_.Module.FlatAlong (A.map j) (A.moduleStage j) := sorry

/-- Flatness of the limiting module is eventually visible at all sufficiently
large stages of a finite-type finite-module approximation.  This specializes
`ModuleSystem.eventually_flat` along `A.toSystem`. -/
@[stacks 00R1 "flatness in a finite-type approximation"]
theorem eventually_flat (A : Module f M)
    (hflat : _root_.Module.FlatAlong f M) :
    ∃ i₀ : A.index, ∀ j, i₀ ≤ j →
      _root_.Module.FlatAlong (A.map j) (A.moduleStage j) := sorry

end Module

end Ring.DirectLimit.Algebra.Approximation
