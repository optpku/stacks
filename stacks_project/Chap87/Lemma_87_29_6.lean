module

public import ReasLib.RingTheory.Topology.FiniteType.Taut
import StacksCheckRecall

@[expose] public section

open TopologicalRing

universe u

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/- Lemma 87.29.6 (1): The four conditions for a continuous arrow of countably
indexed weakly admissible rings are equivalent. -/
@[stacks 0ANU] #check (RingHom.taut_topologicallyOfFiniteType_tfae :
  ∀ {φ : B →+* A}, Continuous φ →
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries])

#check (RingHom.isTaut_and_isFiniteTypeOnWeakIdealQuotients_iff :
  ∀ {φ : B →+* A}, Continuous φ →
    ((φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType))

#check (RingHom.isTaut_and_isFiniteTypeOnCofinalWeakIdealQuotients_iff :
  ∀ {φ : B →+* A}, Continuous φ →
    ((φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType))

#check (RingHom.taut_finiteType_iff_closedQuotient :
  ∀ {φ : B →+* A}, Continuous φ →
    ((φ.IsTaut ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries))

/- Lemma 87.29.6 (2): These equivalent conditions satisfy all three locality
axioms for arrows of countably indexed weakly admissible rings. -/
@[stacks 0ANU] #check
  (TopologicalRing.isLocalMorphismProperty_isTaut_and_topologicallyOfFiniteType :
    TopologicalRing.IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut ∧ φ.TopologicallyOfFiniteType)
