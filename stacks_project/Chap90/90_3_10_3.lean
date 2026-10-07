module

public import ReasLib.RingTheory.Kaehler.ExtendedConormal
import StacksCheckRecall

/-!
# Functoriality of the extended conormal sequence

A map of `Λ`-algebras `B → A` equipped with compatible `Λ`-algebra surjections
onto a common `k` induces a commutative diagram of extended conormal sequences
with exact rows. The outer vertical maps are identities on `H1Cotangent Λ k`
and on `Ω[k⁄Λ]`.
-/

@[expose] public section

open Algebra KaehlerDifferential
open scoped TensorProduct

universe u v w x

/- 90.3.10.3 (1) For a map of `Λ`-algebras `B → A` equipped with compatible
`Λ`-algebra surjections onto `k`, the square relating
`H1Cotangent Λ k → ker(B → k)/ker²` and `H1Cotangent Λ k → ker(A → k)/ker²`
commutes. The outer vertical map is the identity on `H1Cotangent Λ k`. -/
@[stacks 06S8]
#check (Algebra.H1Cotangent.toKerCotangent_naturality :
  ∀ (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)),
    Algebra.H1Cotangent.kerCotangentMap B A k hB hA ∘ₗ
      Algebra.H1Cotangent.toKerCotangent Λ B k hB =
        Algebra.H1Cotangent.toKerCotangent Λ A k hA)

/- 90.3.10.3 (2) In the same tower, the square relating the conormal maps
`d_B` and `d_A` commutes: `tensorMapBaseChange` intertwines the `k`-linear
extensions of `kerCotangentToTensor`. -/
@[stacks 06S8]
#check (KaehlerDifferential.kerCotangentToTensor_naturality :
  ∀ (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k]
    (hB : Function.Surjective (algebraMap B k))
    (hA : Function.Surjective (algebraMap A k)),
    tensorMapBaseChange Λ B A k ∘ₗ kerCotangentToTensor_extend Λ B k hB =
      kerCotangentToTensor_extend Λ A k hA ∘ₗ
        Algebra.H1Cotangent.kerCotangentMap B A k hB hA)

/- 90.3.10.3 (3) In the same tower, the square relating the Kähler base-change
maps to `Ω[k⁄Λ]` commutes, so the outer vertical map on `Ω[k⁄Λ]` is the
identity. -/
@[stacks 06S8]
#check (KaehlerDifferential.mapBaseChange_comp_tensorMapBaseChange :
  ∀ (Λ : Type u) (B : Type v) (A : Type w) (k : Type x)
    [CommRing Λ] [CommRing B] [CommRing A] [CommRing k]
    [Algebra Λ B] [Algebra Λ A] [Algebra Λ k]
    [Algebra B A] [Algebra B k] [Algebra A k]
    [IsScalarTower Λ B A] [IsScalarTower Λ B k] [IsScalarTower Λ A k] [IsScalarTower B A k],
    mapBaseChange Λ A k ∘ₗ tensorMapBaseChange Λ B A k = mapBaseChange Λ B k)

#check (KaehlerDifferential.exact_toKerCotangent_kerCotangentToTensor_extend :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    Function.Exact (Algebra.H1Cotangent.toKerCotangent Λ A k h)
      (kerCotangentToTensor_extend Λ A k h))

#check (KaehlerDifferential.exact_kerCotangentToTensor_extend_mapBaseChange :
  ∀ (Λ : Type u) (A : Type v) (k : Type w)
    [CommRing Λ] [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra Λ k] [Algebra A k] [IsScalarTower Λ A k]
    (h : Function.Surjective (algebraMap A k)),
    Function.Exact (kerCotangentToTensor_extend Λ A k h) (mapBaseChange Λ A k))

#check (KaehlerDifferential.mapBaseChange_surjective :
    ∀ (Λ : Type u) [CommRing Λ] (A : Type v) (k : Type w)
    [CommRing A] [CommRing k]
    [Algebra Λ A] [Algebra A k] [Algebra Λ k] [IsScalarTower Λ A k],
    Function.Surjective (algebraMap A k) → Function.Surjective (mapBaseChange Λ A k))
