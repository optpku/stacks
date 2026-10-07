module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flatness along a ring homomorphism

`Module.Flat` is stated for an explicit scalar action.  This small predicate
records the common situation in which the action is obtained by restricting
scalars along a specified ring homomorphism.  It keeps source-facing
statements independent of proof-local `let` bindings while leaving the
noncanonical action out of global typeclass search.
-/

universe u v w

namespace Module

/-- Flatness of an `A`-module after restricting scalars along `f : R →+* A`. -/
@[stacks 00HD "flatness along a ring homomorphism"]
def FlatAlong
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (M : Type w) [AddCommMonoid M] [Module A M] : Prop :=
  @Module.Flat R M _ _ (Module.compHom M f)

/-- Unfolding lemma for flatness after restriction of scalars. -/
@[simp, stacks 00HD "flatness along a ring homomorphism"]
theorem flatAlong_iff
    {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (M : Type w) [AddCommMonoid M] [Module A M] :
    FlatAlong f M ↔ @Module.Flat R M _ _ (Module.compHom M f) := sorry

end Module
