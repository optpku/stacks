module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dependent-product algebra maps

The pointwise algebra structure on a dependent product uses the component
algebra maps in every coordinate.
-/

universe u v w

namespace Pi

/-- The algebra map between dependent products is the component algebra map at every index. -/
@[stacks 0CY9 "dependent-product algebra-map coordinate formula", simp]
theorem algebraMap_forall_apply {ι : Type u} {R : ι → Type v} {S : ι → Type w}
    [∀ i, CommSemiring (R i)] [∀ i, Semiring (S i)] [∀ i, Algebra (R i) (S i)]
    (x : ∀ i, R i) (i : ι) :
    algebraMap (∀ i, R i) (∀ i, S i) x i = algebraMap (R i) (S i) (x i) := sorry

end Pi
