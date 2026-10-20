module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Weakly.Characterization
public import ReasLib.RingTheory.Topology.Adic.Weakly.Completion

@[expose] public section

universe u

open scoped Topology
open TopologicalRing IsLinearTopology

/- Lemma 87.7.2
Weak pre-adicity is equivalent to a taut pre-adic presentation and to the
existential and universal open-power-closure criteria for ideals of definition.
-/
@[stacks 0GXF] #check (TopologicalRing.IsWeaklyPreadicRing.tfae :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A],
    List.TFAE
      [ IsWeaklyPreadicRing A
      , Nonempty (TautPreadicHom.{u, u} A)
      , IsPreadmissibleRing A ∧
          ∃ I : Ideal A, Ideal.IsIdealOfDefinition I ∧
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A)
      , IsPreadmissibleRing A ∧
          ∀ I : Ideal A, Ideal.IsIdealOfDefinition I →
            ∀ n : ℕ, 1 ≤ n → IsOpen ((I ^ n).closure : Set A) ])

#check (TopologicalRing.IsWeaklyAdicRing.instCompletion :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyPreadicRing A],
    IsWeaklyAdicRing (Completion A A))

#check (TopologicalRing.instIsAdmissibleRing_of_isWeaklyAdicRing :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdicRing A],
    IsAdmissibleRing A)

#check (TopologicalRing.instIsCountablyGenerated_nhds_of_isWeaklyAdicRing :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdicRing A],
    (nhds (0 : A)).IsCountablyGenerated)
