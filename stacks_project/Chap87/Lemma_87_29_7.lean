/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Admissible
import StacksCheckRecall

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

section

variable {B A : Type u} [CommRing B] [TopologicalSpace B]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

#check (RingHom.IsFiniteTypeOnSomeIdealOfDefinition : (B →+* A) → Prop)

#check (RingHom.isFiniteTypeOnSomeIdealOfDefinition_iff :
  ∀ (φ : B →+* A), φ.IsFiniteTypeOnSomeIdealOfDefinition ↔
    ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType)

#check (RingHom.IsFiniteTypeOnSomeIdealOfDefinition.of :
  ∀ {φ : B →+* A} {J : Ideal B}, IsIdealOfDefinition J →
    (φ.closureQuotientMap J).FiniteType → φ.IsFiniteTypeOnSomeIdealOfDefinition)

#check (RingHom.IsFiniteTypeOnSomeIdealOfDefinition.spec :
  ∀ {φ : B →+* A}, φ.IsFiniteTypeOnSomeIdealOfDefinition →
    ∃ J : Ideal B, IsIdealOfDefinition J ∧ (φ.closureQuotientMap J).FiniteType)

end

section

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsAdmissibleRing B] [IsCountablyIndexed B]

/- Lemma 87.29.7: For an admissible source, the four equivalent conditions for a
continuous arrow of countably indexed weakly admissible rings are also equivalent
to tautness and finite type on some ideal-of-definition quotient, whose target
ideal is the closure of the extended source ideal. -/
@[stacks 0CB6] #check (RingHom.taut_topologicallyOfFiniteType_tfae_of_isAdmissibleRing :
  ∀ {φ : B →+* A}, Continuous φ →
    List.TFAE
      [φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients,
        φ.IsTaut ∧ φ.IsFiniteTypeOnCofinalWeakIdealQuotients,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsClosedQuotientOfRestrictedPowerSeries,
        φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition])

#check (RingHom.isTaut_and_isFiniteTypeOnSomeIdealOfDefinition_iff :
  ∀ {φ : B →+* A}, Continuous φ →
    ((φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType))

#check (RingHom.taut_finiteTypeQuotients_iff_someIdealOfDefinition :
  ∀ {φ : B →+* A}, Continuous φ →
    ((φ.IsTaut ∧ φ.IsFiniteTypeOnWeakIdealQuotients) ↔
      φ.IsTaut ∧ φ.IsFiniteTypeOnSomeIdealOfDefinition))

end
