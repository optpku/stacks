module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Definition_88_20_1_Ring

/-!
# Independence of the ideal of definition for rig-étale arrows of WAdm^Noeth
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- `B` is rig-étale over the pair `(A, I)` along `φ`, in the sense of
Definition 88.8.1, using the `A`-algebra structure `φ.toAlgebra`. -/
def IsRigEtaleOver (φ : A →+* B) (I : Ideal A) : Prop :=
  @Algebra.RigEtale A _ I B _ φ.toAlgebra

/-- The RingHom view of rig-étaleness over `(A, I)` is `Algebra.RigEtale`
along `φ.toAlgebra`. -/
theorem isRigEtaleOver_iff (φ : A →+* B) (I : Ideal A) :
    φ.IsRigEtaleOver I ↔ @Algebra.RigEtale A _ I B _ φ.toAlgebra :=
  sorry

variable [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/-- Lemma 88.19.1: Let `φ : A →+* B` be a morphism in `WAdm^Noeth`. The
following are equivalent: `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and there exists an ideal of definition `I ⊂ B` such that `B` is
rig-étale over `(A, I)`; and `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and for every ideal of definition `I` of `A` the algebra `B` is
rig-étale over `(A, I)`.

The source clause with an ideal of definition of `B` is expressed by an ideal
of definition `I` of `A` such that `IsAdic (Ideal.map φ I)`, so that `I B` is an
ideal of definition of `B`, while `IsRigEtaleOver` still takes that `A`-ideal as
in Definition 88.8.1. The Lemma 88.11.1 conditions are represented by
`φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0GCU]
theorem exists_rigEtaleOver_iff_forall {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∃ I : Ideal A,
          IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) ∧ φ.IsRigEtaleOver I) ↔
      (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∀ I : Ideal A, IsIdealOfDefinition I → φ.IsRigEtaleOver I) :=
  sorry

/-- Under the equivalent conditions of Lemma 88.11.1, existence of one ideal of
definition of `A` making `I B` an ideal of definition of `B` and making `B`
rig-étale over `(A, I)` is equivalent to rig-étaleness over `(A, I)` for every
ideal of definition of `A`. -/
theorem isRigEtaleOver_some_iff_forall {φ : A →+* B} (hφ : Continuous φ)
    (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType) :
    (∃ I : Ideal A,
        IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) ∧ φ.IsRigEtaleOver I) ↔
      ∀ I : Ideal A, IsIdealOfDefinition I → φ.IsRigEtaleOver I :=
  sorry

end RingHom
