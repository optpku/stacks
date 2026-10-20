module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness over weakly admissible rings

For flat algebras over a weakly admissible ring, faithful flatness can be tested
after quotienting by weak ideals of definition.
-/

@[expose] public section

universe u v

namespace TopologicalRing

variable (B : Type u) [CommRing B] [TopologicalSpace B]
  (A : Type v) [CommRing A] [Algebra B A]

/-- A flat algebra over a weakly admissible ring is faithfully flat if and only if
its canonical map modulo every weak ideal of definition is faithfully flat. -/
theorem algebraMap_faithfullyFlat_iff_forall_weakIdeal_quotient
    [IsWeaklyAdmissibleRing B] [Module.Flat B A] :
    (algebraMap B A).FaithfullyFlat ↔
      ∀ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J →
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat :=
  sorry

/-- A flat algebra over a weakly admissible ring is faithfully flat if and only if
its canonical map modulo some weak ideal of definition is faithfully flat. -/
theorem algebraMap_faithfullyFlat_iff_exists_weakIdeal_quotient
    [IsWeaklyAdmissibleRing B] [Module.Flat B A] :
    (algebraMap B A).FaithfullyFlat ↔
      ∃ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J ∧
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat :=
  sorry

end TopologicalRing
