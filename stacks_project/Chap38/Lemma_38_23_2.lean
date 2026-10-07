module

public import ReasLib.LinearAlgebra.LinearMap.CoefficientIdeal
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Lemma 38.23.2: a surjective linear map from a projective module admits an ideal whose
image in every scalar extension vanishes exactly when the base-changed map is bijective. -/
@[stacks 05PE] #check
  (LinearMap.exists_ideal_baseChange_bijective_iff :
    ∀ {A : Type u} [CommRing A]
      {M : Type v} [AddCommGroup M] [Module A M]
      {N : Type w} [AddCommGroup N] [Module A N]
      [Module.Projective A M] (u : M →ₗ[A] N), Function.Surjective u →
        ∃ I : Ideal A, ∀ (B : Type x) [CommRing B] [Algebra A B],
          Function.Bijective (u.baseChange B) ↔ I.map (algebraMap A B) = ⊥)
