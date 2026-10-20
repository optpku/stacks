module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Taut.InverseLimit
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Taut.Locality
import StacksCheckRecall

/-!
# Sequential characterization of taut arrows of WAdm^count

A continuous arrow of countably indexed weakly admissible rings is taut if and
only if it admits a sequential inverse-limit presentation along a nested
countable fundamental system of weak ideals of definition, and this property
is local in the sense of Situation 87.21.2.
-/

@[expose] public section

open scoped Topology
open TopologicalRing
open TopologicalRing.Ideal

universe u

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]

/- Lemma 87.22.1 (1): A continuous arrow of countably indexed weakly
admissible rings is taut exactly when a nested fundamental sequence of weak
ideals of definition gives the canonical successive-quotient inverse-limit
presentation. -/
@[stacks 0ANJ] #check (RingHom.isTaut_iff_isTautInverseLimit :
  ∀ {φ : A →+* B}, Continuous φ →
    ∀ {J : ℕ → Ideal A}, (∀ n, IsWeakIdealOfDefinition (J n)) →
      (∀ n, J (n + 1) ≤ J n) →
      (nhds (0 : A)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ (J n : Set A)) →
      (φ.IsTaut ↔ φ.IsTautInverseLimit J))

/- Lemma 87.22.1 (2): Tautness satisfies all three locality axioms of
Situation 87.21.2, including faithfully flat descent and finite products. -/
@[stacks 0ANJ] #check (TopologicalRing.isLocalMorphismProperty_isTaut :
    TopologicalRing.IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsTaut)
