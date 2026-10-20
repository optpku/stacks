module

public import ReasLib.RingTheory.AdicCompletion.RigFlat.Jacobson
import StacksCheckRecall

/-!
# Naive versus rig-flat arrows with Jacobson special fiber

A naively rig-flat arrow of adic Noetherian topological rings is rig-flat as
soon as the special fiber `A ⧸ I` is Jacobson for an ideal of definition of
`A`.
-/

@[expose] public section

universe u

/- For an adic Noetherian topological ring, `A ⧸ I` is Jacobson for some
ideal of definition if and only if it is Jacobson for every ideal of
definition. -/
#check (isJacobsonRing_quotient_isIdealOfDefinition_iff :
    ∀ {A : Type u}
    [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A],
    (∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
        IsJacobsonRing (A ⧸ I)) ↔
      ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I →
        IsJacobsonRing (A ⧸ I))

/- Lemma 88.15.5: an arrow `φ : A →+* B` of `WAdm^{Noeth}` that is naively
rig-flat is rig-flat as soon as `A ⧸ I` is Jacobson for some, equivalently any,
ideal of definition `I` of `A`. -/
@[stacks 0GGQ] #check (RingHom.RigFlat.of_naive :
    ∀ {A B : Type u}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [RingHom.NaiveRigFlat φ] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)],
    RingHom.RigFlat φ)

/- Under the Jacobson special-fiber hypothesis, a homomorphism of adic
Noetherian topological rings is rig-flat if and only if it is naively
rig-flat. -/
#check (RingHom.RigFlat.iff_naive :
    ∀ {A B : Type u}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)],
    RingHom.RigFlat φ ↔ RingHom.NaiveRigFlat φ)
