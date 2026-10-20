module

public import ReasLib.RingTheory.Kaehler.ResidueConormal
import StacksCheckRecall

@[expose]
public section

universe u v w

open scoped TensorProduct

/- 90.3.10.1: for a Noetherian base Λ, a field k finite over Λ, and a
surjective Λ-algebra map A → k, the sequence
(ker (algebraMap A k)).Cotangent ⟶ Ω[A⁄Λ] ⊗[A] k ⟶ Ω[k⁄Λ] ⟶ 0
is exact. Mathlib writes its middle module as k ⊗[A] Ω[A⁄Λ], canonically
corresponding to the source's Ω[A⁄Λ] ⊗[A] k by `TensorProduct.comm`. -/
@[stacks 06S6] #check (KaehlerDifferential.residueConormalSequence_exact :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [IsNoetherianRing Λ] [CommRing A] [Field k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k]
    [Module.Finite Λ k],
    Function.Surjective (algebraMap A k) →
    Function.Exact (KaehlerDifferential.kerCotangentToTensor Λ A k)
      (KaehlerDifferential.mapBaseChange Λ A k) ∧
    Function.Surjective (KaehlerDifferential.mapBaseChange Λ A k))

/- The conormal map sends the cotangent module of ker (algebraMap A k) to the
fiber of Ω[A⁄Λ] over k. -/
#check (KaehlerDifferential.kerCotangentToTensor :
  ∀ (Λ : Type u) [CommRing Λ] (A : Type v) (k : Type w)
    [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k],
    (RingHom.ker (algebraMap A k)).Cotangent →ₗ[A] k ⊗[A] Ω[A⁄Λ])

/- The base-change map takes the differential fiber to Ω[k⁄Λ]. -/
#check (KaehlerDifferential.mapBaseChange :
  ∀ (Λ : Type u) [CommRing Λ] (A : Type v) (k : Type w)
    [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k],
    k ⊗[A] Ω[A⁄Λ] →ₗ[k] Ω[k⁄Λ])

/- The map from the differential fiber to Ω[k⁄Λ] is surjective. -/
#check (KaehlerDifferential.mapBaseChange_surjective :
  ∀ (Λ : Type u) [CommRing Λ] (A : Type v) (k : Type w)
    [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k],
    Function.Surjective (algebraMap A k) →
      Function.Surjective (KaehlerDifferential.mapBaseChange Λ A k))
