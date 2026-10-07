module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap88.Definition_88_18_1_Ring

/-!
# Independence of the ideal of definition for rig-smooth arrows of WAdm^Noeth
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]

/-- Lemma 88.17.1: Let `φ : A →+* B` be a morphism in `WAdm^Noeth`. The
following are equivalent: `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and there exists an ideal of definition of `B` such that `B` is
rig-smooth over `(A, I)`; and `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and for every ideal of definition `I` of `A` the algebra `B` is
rig-smooth over `(A, I)`.

The source clause with an ideal of definition of `B` is expressed by an ideal
of definition `I` of `A` such that `IsAdic (Ideal.map φ I)`, so that `IB` is an
ideal of definition of `B`, while `Algebra.RigSmooth` still takes that `A`-ideal
as in Definition 88.4.1. The Lemma 88.11.1 conditions are represented by
`φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0GCI]
theorem exists_rigSmooth_iff_forall_idealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) :
    ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∃ I : Ideal A,
          TopologicalRing.Ideal.IsIdealOfDefinition I ∧
            IsAdic (Ideal.map φ I) ∧
              @Algebra.RigSmooth A _ I B _ φ.toAlgebra) ↔
      ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
          @Algebra.RigSmooth A _ I B _ φ.toAlgebra) :=
  sorry

/-- Under the equivalent conditions of Lemma 88.11.1, `Algebra.RigSmooth I B`
via `φ` is independent of the choice of ideal of definition of `A`. -/
theorem rigSmooth_independentOfIdealOfDefinition {φ : A →+* B}
    (hφ : Continuous φ) (h : φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
    {I I' : Ideal A} (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (hI' : TopologicalRing.Ideal.IsIdealOfDefinition I') :
    @Algebra.RigSmooth A _ I B _ φ.toAlgebra ↔
      @Algebra.RigSmooth A _ I' B _ φ.toAlgebra :=
  sorry

end RingHom
