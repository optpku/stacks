module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite modules under simultaneous universe lifting

This leaf records the finite-generation transport that changes both the base
semiring and the module universe.  The scalar action is deliberately an input:
`ULift.algebra'` cannot be a global instance without creating instance
diamonds.
-/

namespace Module.Finite

universe u v w x

/-- A finite `R`-module remains finite after simultaneously lifting the base semiring and the
module, relative to a chosen compatible lifted scalar action. -/
@[stacks 0CAR "finite modules under a lifted base semiring"]
theorem uliftBase
    {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module (ULift.{w} R) (ULift.{x} M)]
    [IsScalarTower R (ULift.{w} R) (ULift.{x} M)]
    (hM : Module.Finite R M) :
    Module.Finite (ULift.{w} R) (ULift.{x} M) := sorry

end Module.Finite
