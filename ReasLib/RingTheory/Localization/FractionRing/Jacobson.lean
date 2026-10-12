/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobson-radical denominators in common fraction fields

This leaf records a finite-family denominator choice whose inverses lie in the
Jacobson radicals of one-dimensional semilocal domains sharing a fraction
field.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace FractionRing.Jacobson

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type v} [Field K] [Algebra A K]
variable {ι : Type w}
variable {B : ι → Type w}
variable [hComm : ∀ i, CommRing (B i)] [hDomain : ∀ i, IsDomain (B i)]
variable [hAlgebra : ∀ i, Algebra (B i) K]

include hComm hDomain hAlgebra

/-- If a domain and a finite family of Noetherian one-dimensional semilocal domains have a
common fraction field and their tensor comparison maps are surjective, then one nonzero element
of the domain has inverse in the Jacobson radical of every component. -/
@[stacks 09N5]
theorem exists_nonzero_with_inv_mem_jacobson
    [Finite ι] (hFractionA : IsFractionRing A K)
    (hFraction : ∀ i, IsFractionRing (B i) K)
    (hNoetherian : ∀ i, IsNoetherianRing (B i))
    (hSemilocal : ∀ i, Finite (MaximalSpectrum (B i)))
    (hdim : ∀ i, ringKrullDim (B i) = 1)
    (hsurj : ∀ i,
      Function.Surjective
        ((Algebra.TensorProduct.productMap
            (IsScalarTower.toAlgHom ℤ A K)
            (IsScalarTower.toAlgHom ℤ (B i) K)) : A ⊗[ℤ] B i →ₐ[ℤ] K)) :
    ∃ x : A, x ≠ 0 ∧ ∀ i,
      ∃ y : Ring.jacobson (B i), algebraMap (B i) K y = (algebraMap A K x)⁻¹ := sorry

end FractionRing.Jacobson
