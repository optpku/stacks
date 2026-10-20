module

public import ReasLib.RingTheory.Topology.Adic.Descent
import StacksCheckRecall

/-!
# Lemma 87.8.5

Adic rings with a finitely generated ideal of definition descend along a
continuous taut homomorphism of linearly topologized rings with faithfully
flat open quotients, when the source is complete.
-/

@[expose] public section

universe u v

namespace TopologicalRing.IsAdicRing

/- Lemma 87.8.5 (1): In the situation above, if `B` is adic and has a finitely
generated ideal of definition and `A` is complete, then `A` is adic. The
situation is a continuous taut homomorphism `φ : A →+* B` of linearly
topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every open
ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. Completeness of `A` means
separatedness together with completeness of the additive uniformity. -/
@[stacks 0GXQ] #check (TopologicalRing.IsAdicRing.of_faithfullyFlatOpenQuotients :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
      (∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) → IsAdicRing A)

/- Lemma 87.8.5 (2): In the situation above, if `B` is adic and has a finitely
generated ideal of definition and `A` is complete, then `A` has a finitely
generated ideal of definition. -/
@[stacks 0GXQ] #check (TopologicalRing.IsAdicRing.exists_fg_isIdealOfDefinition :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
      (∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) →
      ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I)

end TopologicalRing.IsAdicRing
