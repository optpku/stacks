module

public import ReasLib.RingTheory.Topology.Adic.Taut
import StacksCheckRecall

/-!
# Lemma 87.6.5

A continuous taut homomorphism from a pre-adic ring with a finitely generated
ideal of definition into a complete linearly topologized ring is adic, and the
target is adic with a finitely generated ideal of definition.
-/

@[expose] public section

universe u v

open TopologicalRing

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [T2Space B] [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]

/- Lemma 87.6.5 (1): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `B` is adic. -/
@[stacks 0APU] #check (RingHom.IsTaut.isAdicRing :
  ∀ {φ : A →+* B}, Continuous φ → φ.IsTaut →
    (∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) →
    IsAdicRing B)

/- Lemma 87.6.5 (2): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `B` has a finitely generated
ideal of definition. -/
@[stacks 0APU] #check (RingHom.IsTaut.exists_fg_isIdealOfDefinition :
  ∀ {φ : A →+* B}, Continuous φ → φ.IsTaut →
    (∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) →
    ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J)

/- Lemma 87.6.5 (3): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut, `A` is pre-adic and has a finitely generated
ideal of definition, and `B` is complete, then `φ` is adic. -/
@[stacks 0APU] #check (RingHom.IsTaut.exists_isAdic_map :
  ∀ {φ : A →+* B}, Continuous φ → φ.IsTaut →
    (∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) →
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
      IsAdic (Ideal.map φ I))
