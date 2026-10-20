module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.IdealOfDefinition
import StacksCheckRecall

/-!
# Independence of the ideal of definition for rig-étale arrows of WAdm^Noeth
-/

@[expose] public section

universe u

open TopologicalRing
open TopologicalRing.Ideal

/- Lemma 88.19.1: Let `φ : A →+* B` be a morphism in `WAdm^Noeth`. The
following are equivalent: `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and there exists an ideal of definition `I ⊂ B` such that `B` is
rig-étale over `(A, I)`; and `φ` satisfies the equivalent conditions of
Lemma 88.11.1 and for every ideal of definition `I` of `A` the algebra `B` is
rig-étale over `(A, I)`.

The definition and proof require `I` to be an ideal of `A`. The source clause
with an ideal of definition of `B` is expressed by an ideal of definition `I`
of `A` such that `IsAdic (Ideal.map φ I)`: adicity ensures its extension `I B`
is an ideal of definition of `B`, while `IsRigEtaleOver` takes that `A`-ideal
as in Definition 88.8.1. The Lemma 88.11.1 conditions are represented by
`φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0GCU] #check (RingHom.exists_rigEtaleOver_iff_forall :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    {φ : A →+* B}, Continuous φ →
    ((φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∃ I : Ideal A,
          IsIdealOfDefinition I ∧ IsAdic (Ideal.map φ I) ∧ φ.IsRigEtaleOver I) ↔
      (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType ∧
        ∀ I : Ideal A, IsIdealOfDefinition I → φ.IsRigEtaleOver I)))
