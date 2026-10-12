/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.ExtendedConormal
import StacksCheckRecall

/-!
# Extended naive-cotangent sequence

For a `Λ`-algebra `A` equipped with a `Λ`-algebra surjection `A → k` (in particular any object
of `C_Λ`), the naive-cotangent Jacobi–Zariski sequence of `Λ → A → k` extends the conormal
sequence to
`H1Cotangent Λ k → (ker (algebraMap A k)).Cotangent → k ⊗[A] Ω[A⁄Λ] → Ω[k⁄Λ] → 0`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct
open Algebra Algebra.Extension KaehlerDifferential

/- 90.3.10.2 (1): the first arrow `H1Cotangent Λ k → (ker (algebraMap A k)).Cotangent`
of the extended naive-cotangent sequence. -/
@[stacks 06S7]
#check (Algebra.H1Cotangent.toKerCotangent :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    H1Cotangent Λ k →ₗ[k] (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent)

/- 90.3.10.2 (2): the source map `d_A` is `kerCotangentToTensor_extend`, landing in
`k ⊗[A] Ω[A⁄Λ]` (mathlib tensor order). -/
@[stacks 06S7]
#check (KaehlerDifferential.kerCotangentToTensor_extend :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k]
    (h : Function.Surjective (algebraMap A k)),
    (Extension.ofSurjective (Algebra.ofId A k) h).Cotangent →ₗ[k] k ⊗[A] Ω[A⁄Λ])

/- 90.3.10.2 (3): exactness at `m_A / m_A²`, i.e. at `(ker (algebraMap A k)).Cotangent`. -/
@[stacks 06S7]
#check (KaehlerDifferential.exact_toKerCotangent_kerCotangentToTensor_extend :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    Function.Exact (Algebra.H1Cotangent.toKerCotangent Λ A k h)
      (kerCotangentToTensor_extend Λ A k h))

/- 90.3.10.2 (4): exactness at `Ω[A⁄Λ] ⊗[A] k`, i.e. at `k ⊗[A] Ω[A⁄Λ]`. -/
@[stacks 06S7]
#check (KaehlerDifferential.exact_kerCotangentToTensor_extend_mapBaseChange :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    Function.Exact (kerCotangentToTensor_extend Λ A k h) (mapBaseChange Λ A k))

/- 90.3.10.2 (5): the terminal map `k ⊗[A] Ω[A⁄Λ] → Ω[k⁄Λ]` is surjective. -/
@[stacks 06S7]
#check (KaehlerDifferential.ExtendedConormal.mapBaseChange_surjective :
  ∀ (Λ : Type u) [CommRing Λ] (A : Type v) (k : Type w)
    [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k],
    Function.Surjective (algebraMap A k) → Function.Surjective (mapBaseChange Λ A k))
