module

public import ReasLib.RingTheory.Topology.Adic.Basic

/-!
# Primes avoiding ideals of definition

Ideal avoidance and maximality describe points and closed points of the
complement of the zero locus of an ideal of definition.
-/

@[expose] public section

universe u

namespace Ideal

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- An ideal contains no topological ideal of definition of the ambient ring. -/
def ContainsNoIdealOfDefinition (q : Ideal A) : Prop :=
  ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q

/-- Unfold `ContainsNoIdealOfDefinition` as the absence of a contained ideal of
definition. -/
theorem containsNoIdealOfDefinition_iff (q : Ideal A) :
    q.ContainsNoIdealOfDefinition ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q :=
  Iff.rfl

namespace ContainsNoIdealOfDefinition

/-- A contained topological ideal of definition is forbidden. -/
theorem apply {q : Ideal A} (hq : q.ContainsNoIdealOfDefinition) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) : ¬ I ≤ q :=
  hq I hI

end ContainsNoIdealOfDefinition

/-- A prime is maximal among primes omitting some topological ideal of definition.
It represents a closed point of the complement of the zero locus of that ideal.
For Noetherian adic rings, this agrees with the rig-closed-prime convention. -/
def IsMaximalAvoidingIdealOfDefinition (q : Ideal A) : Prop :=
  q.IsPrime ∧
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
        ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q

/-- Unfold `IsMaximalAvoidingIdealOfDefinition` as primeness together with
maximality among primes omitting some topological ideal of definition. -/
theorem isMaximalAvoidingIdealOfDefinition_iff (q : Ideal A) :
    q.IsMaximalAvoidingIdealOfDefinition ↔
      q.IsPrime ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
            ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q :=
  Iff.rfl

namespace IsMaximalAvoidingIdealOfDefinition

/-- Such an ideal is prime. -/
theorem isPrime {q : Ideal A} (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    q.IsPrime :=
  hq.1

/-- There is a topological ideal of definition omitted by `q`, and `q` is
maximal among primes with that property. -/
theorem exists_idealOfDefinition {q : Ideal A}
    (hq : q.IsMaximalAvoidingIdealOfDefinition) :
    ∃ I : Ideal A,
      TopologicalRing.Ideal.IsIdealOfDefinition I ∧ ¬ I ≤ q ∧
        ∀ r : Ideal A, r.IsPrime → ¬ I ≤ r → q ≤ r → r = q :=
  hq.2

end IsMaximalAvoidingIdealOfDefinition

end Ideal
