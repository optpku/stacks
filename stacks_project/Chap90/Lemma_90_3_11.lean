module

public import Mathlib.FieldTheory.Separable
public import stacks_project.Chap90.Lemma_90_3_11_Comparison
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 90.3.11 (1): there is a canonical map
`(ker (algebraMap Λ k)).Cotangent ⟶ H1Cotangent Λ k` from
`m_Λ / m_Λ²` to `H¹(L_{k/Λ})`. -/
@[stacks 06S9] #check Algebra.H1Cotangent.ofKerCotangent

namespace Algebra.H1Cotangent

/-- Lemma 90.3.11 (2): if `k' ⊆ k` is separable (for example if the characteristic
of `k` is zero), then `ofKerCotangentBaseChange` is a `k`-linear isomorphism
`k ⊗[k'] (ker (algebraMap Λ k)).Cotangent ≃ H1Cotangent Λ k`. -/
@[stacks 06S9]
theorem bijective_ofKerCotangentBaseChange
    (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] [Algebra.IsIntegral Λ k]
    [Algebra.IsSeparable (residueImage Λ k) k] :
    Function.Bijective (ofKerCotangentBaseChange Λ k) :=
  sorry

/-- Lemma 90.3.11 (3): if `k = k'` (for example in the classical case), then
`equivKerCotangent` identifies `(ker (algebraMap Λ k)).Cotangent` with
`H1Cotangent Λ k` as modules over `residueImage Λ k`. -/
@[stacks 06S9]
theorem equivKerCotangent_identifies
    (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k]
    (h : Function.Surjective (algebraMap Λ k))
    (x : (RingHom.ker (algebraMap Λ k)).Cotangent) :
    equivKerCotangent Λ k h x = ofKerCotangent Λ k x :=
  sorry

/-- Lemma 90.3.11 (4): for a `Λ`-algebra `A` equipped with a `Λ`-algebra surjection
`A → k`, the composite
`(ker (algebraMap Λ k)).Cotangent ⟶ H1Cotangent Λ k ⟶ (ker (algebraMap A k)).Cotangent`
agrees with the map induced by `ker (algebraMap Λ k) → ker (algebraMap A k)`. -/
@[stacks 06S9]
theorem ofKerCotangent_comp_toKerCotangent
    (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [Field k] [Algebra Λ k]
    [Algebra Λ A] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)) :
    (toKerCotangent Λ A k h).comp ((ofKerCotangent Λ k).restrictScalars Λ) =
      Ideal.mapCotangent (RingHom.ker (algebraMap Λ k)) (RingHom.ker (algebraMap A k))
        (Algebra.ofId Λ A) (ker_le_comap_ker_of_tower Λ A k) :=
  sorry

end Algebra.H1Cotangent
