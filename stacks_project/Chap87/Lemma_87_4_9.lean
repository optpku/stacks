module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible

/-!
# Lemma 87.4.9

A weakly admissible topological ring together with a weak ideal of definition
is a henselian pair.
-/

@[expose] public section

universe u

namespace TopologicalRing.Ideal.IsWeakIdealOfDefinition

/-- Lemma 87.4.9: Let `A` be a weakly admissible topological ring. Let `I ⊆ A` be a
weak ideal of definition. Then `(A, I)` is a henselian pair. -/
@[stacks 0DCZ]
theorem henselianRing {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsWeaklyAdmissibleRing A] {I : Ideal A}
    (hI : IsWeakIdealOfDefinition I) : HenselianRing A I := sorry

end TopologicalRing.Ideal.IsWeakIdealOfDefinition
