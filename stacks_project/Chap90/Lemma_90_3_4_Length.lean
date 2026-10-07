module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Length comparison along a possibly non-local base

The image field `residueImage Λ k` is `k' = Λ ⧸ ker(algebraMap Λ k)`. For a local
`Λ`-algebra `A`, module length over `Λ` and over `A` differ by the length of the
residue field of `A` as a `k'`-module.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Algebra

/-- The image field `k' = Λ ⧸ ker(algebraMap Λ k)` of a map from a ring to a field. -/
abbrev residueImage (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] : Type u :=
  Λ ⧸ RingHom.ker (algebraMap Λ k)

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The kernel of `algebraMap Λ k` is maximal when `k` is integral over `Λ`. -/
instance residueImage.instIsMaximal [Algebra.IsIntegral Λ k] :
    (RingHom.ker (algebraMap Λ k)).IsMaximal :=
  ker_algebraMap_isMaximal_of_isIntegral Λ k

/-- The image `residueImage Λ k` is a field. -/
noncomputable instance residueImage.instField [Algebra.IsIntegral Λ k] :
    Field (residueImage Λ k) :=
  Ideal.Quotient.field _

/-- Scalar multiplication of `k` through the image field `residueImage Λ k`. -/
instance residueImage.instAlgebra : Algebra (residueImage Λ k) k :=
  (RingHom.kerLift (algebraMap Λ k)).toAlgebra

/-- The tower `Λ → residueImage Λ k → k`. -/
instance residueImage.instIsScalarTower : IsScalarTower Λ (residueImage Λ k) k :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Finiteness of `k` over `Λ` implies finiteness over the image field. -/
instance residueImage.instFinite [Module.Finite Λ k] :
    Module.Finite (residueImage Λ k) k :=
  Module.Finite.of_restrictScalars_finite Λ (residueImage Λ k) k

/-- The canonical map `Λ → residueImage Λ k` is surjective. -/
theorem residueImage.algebraMap_surjective :
    Function.Surjective (algebraMap Λ (residueImage Λ k)) :=
  sorry

/-- Over the image field, length of `k` agrees with `Module.finrank`. -/
theorem residueImage.length_eq_finrank [Module.Finite Λ k] :
    Module.length (residueImage Λ k) k = Module.finrank (residueImage Λ k) k :=
  sorry

/-- First isomorphism theorem: a surjective map `Λ → k` identifies `residueImage Λ k` with `k`. -/
noncomputable def residueImage.algEquivOfSurjective
    (hsurj : Function.Surjective (algebraMap Λ k)) :
    residueImage Λ k ≃ₐ[Λ] k :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Λ k) hsurj

/-- The first-isomorphism equivalence sends the class of `x` to `algebraMap Λ k x`. -/
theorem residueImage.algEquivOfSurjective_mk
    (hsurj : Function.Surjective (algebraMap Λ k)) (x : Λ) :
    residueImage.algEquivOfSurjective hsurj
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = algebraMap Λ k x :=
  sorry

/-- When `Λ` is local, the image field is the residue field of `Λ`. -/
def residueImage.equivResidueField [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    [Algebra.IsIntegral Λ k] :
    residueImage Λ k ≃ₐ[Λ] ResidueField Λ :=
  (Ideal.quotientEquivAlgOfEq Λ
    (eq_maximalIdeal (ker_algebraMap_isMaximal_of_isIntegral Λ k)) :
    residueImage Λ k ≃ₐ[Λ] ResidueField Λ)

/-- The residue-field identification sends the class of `x` to `residue x`. -/
theorem residueImage.equivResidueField_mk [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    [Algebra.IsIntegral Λ k] (x : Λ) :
    residueImage.equivResidueField
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = residue Λ x :=
  sorry

end Algebra

namespace IsLocalRing

open Algebra

/-- Length over `Λ` is length over a local algebra `A` times the length of `κ(A)` over the
image field of `Λ → κ(A)`. -/
theorem length_eq_mul_length_residueImage {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Algebra.IsIntegral Λ (ResidueField A)] :
    Module.length Λ M =
      Module.length A M *
        Module.length (residueImage Λ (ResidueField A)) (ResidueField A) :=
  sorry

/-- Finite-degree form of `length_eq_mul_length_residueImage`, with multiplier
`Module.finrank` of the residue field over the image field. -/
theorem length_eq_mul_finrank_residueImage {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Module.Finite Λ (ResidueField A)] :
    Module.length Λ M =
      Module.length A M *
        (Module.finrank (residueImage Λ (ResidueField A)) (ResidueField A) : ℕ∞) :=
  sorry

end IsLocalRing
