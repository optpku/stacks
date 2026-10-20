module

public import Mathlib.FieldTheory.Separable
public import ReasLib.RingTheory.Extension.Cotangent.KernelComparison
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 90.3.11 (1): there is a canonical map
`(ker (algebraMap Λ k)).Cotangent ⟶ H1Cotangent Λ k` from
`m_Λ / m_Λ²` to `H¹(L_{k/Λ})`. -/
@[stacks 06S9]
#check (Algebra.H1Cotangent.ofKerCotangent : ∀ (Λ : Type u) (k : Type v)
  [CommRing Λ] [Field k] [Algebra Λ k],
  (RingHom.ker (algebraMap Λ k)).Cotangent →ₗ[Algebra.residueImage Λ k]
    Algebra.H1Cotangent Λ k)

/- Lemma 90.3.11 (2): if `k' ⊆ k` is separable, then the induced base-change map is bijective. -/
@[stacks 06S9]
#check (Algebra.H1Cotangent.bijective_ofKerCotangentBaseChange : ∀ (Λ : Type u) (k : Type v)
  [CommRing Λ] [Field k] [Algebra Λ k] [Algebra.IsIntegral Λ k]
  [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
  Function.Bijective (Algebra.H1Cotangent.ofKerCotangentBaseChange Λ k))

/- Lemma 90.3.11 (3): if `k = k'`, then the canonical comparison agrees pointwise with
the kernel-cotangent equivalence. -/
@[stacks 06S9]
#check (Algebra.H1Cotangent.ofKerCotangent_eq_equivKerCotangent : ∀
  (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k]
  (h : Function.Surjective (algebraMap Λ k))
  (x : (RingHom.ker (algebraMap Λ k)).Cotangent),
  Algebra.H1Cotangent.equivKerCotangent Λ k h x =
    Algebra.H1Cotangent.ofKerCotangent Λ k x)

/- Lemma 90.3.11 (4): for a surjective `Λ`-algebra map `A → k`, the composite comparison
is induced by the inclusion of kernels. -/
@[stacks 06S9]
#check (Algebra.H1Cotangent.ofKerCotangent_comp_toIdealKerCotangent : ∀
  (Λ : Type u) (A : Type v) (k : Type w)
  [CommRing Λ] [CommRing A] [Field k] [Algebra Λ k]
  [Algebra Λ A] [Algebra A k] [IsScalarTower Λ A k]
  (h : Function.Surjective (algebraMap A k)),
  (Algebra.H1Cotangent.toIdealKerCotangent Λ A k h).comp
      ((Algebra.H1Cotangent.ofKerCotangent Λ k).restrictScalars Λ) =
    Ideal.mapCotangent (RingHom.ker (algebraMap Λ k))
      (RingHom.ker (algebraMap A k)) (Algebra.ofId Λ A)
      (Algebra.H1Cotangent.ker_le_comap_ker_of_tower Λ A k))
