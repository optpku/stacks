module

public import ReasLib.Algebra.Algebra.ResidueImage
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Length comparison along a possibly non-local base

The image field `residueImage Λ k` is `Λ ⧸ ker(algebraMap Λ k)`. For a local
`Λ`-algebra `A`, module length over `Λ` and over `A` differ by the degree of the
residue field of `A` over the image field.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Algebra

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The canonical map `Λ → residueImage Λ k` is surjective. -/
theorem residueImage.algebraMap_surjective :
    Function.Surjective (algebraMap Λ (residueImage Λ k)) := sorry

/-- A surjective map `Λ → k` identifies `residueImage Λ k` with `k`. -/
noncomputable def residueImage.algEquivOfSurjective
    (hsurj : Function.Surjective (algebraMap Λ k)) :
    residueImage Λ k ≃ₐ[Λ] k :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId Λ k) hsurj

/-- The equivalence induced by a surjection maps the class of `x` to `algebraMap Λ k x`. -/
theorem residueImage.algEquivOfSurjective_mk
    (hsurj : Function.Surjective (algebraMap Λ k)) (x : Λ) :
    residueImage.algEquivOfSurjective hsurj
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = algebraMap Λ k x := sorry

/-- For a local base ring, the image field is its residue field. -/
def residueImage.equivResidueField [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    [Algebra.IsIntegral Λ k] :
    residueImage Λ k ≃ₐ[Λ] ResidueField Λ :=
  (Ideal.quotientEquivAlgOfEq Λ
    (eq_maximalIdeal (ker_algebraMap_isMaximal_of_isIntegral Λ k)) :
    residueImage Λ k ≃ₐ[Λ] ResidueField Λ)

/-- The residue-field equivalence maps the class of `x` to `residue Λ x`. -/
theorem residueImage.equivResidueField_mk [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    [Algebra.IsIntegral Λ k] (x : Λ) :
    residueImage.equivResidueField
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = residue Λ x := sorry

end Algebra

namespace IsLocalRing

open Algebra

/-- Length over `Λ` is length over a local algebra `A` times the length of its residue
field over the image field of `Λ → ResidueField A`. -/
theorem length_eq_mul_length_residueImage {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Algebra.IsIntegral Λ (ResidueField A)] :
    Module.length Λ M =
      Module.length A M *
        Module.length (residueImage Λ (ResidueField A)) (ResidueField A) := sorry

/-- Length over `Λ` is length over a local algebra `A` times the finite dimension of its
residue field over the image field of `Λ → ResidueField A`. -/
theorem length_eq_mul_finrank_residueImage {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Module.Finite Λ (ResidueField A)] :
    Module.length Λ M =
      Module.length A M *
        (Module.finrank (residueImage Λ (ResidueField A)) (ResidueField A) : ℕ∞) := sorry

/-- If the residue field of a local `Λ`-algebra `A` is identified with a finite
`Λ`-algebra `k`, then restriction of scalars multiplies length by the degree of `k`
over the image field of `Λ → k`. -/
theorem length_mul_finrank_eq_length {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    {A : Type v} [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (residueFieldIso : ResidueField A ≃ₐ[Λ] k) {M : Type w}
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] :
    (Module.finrank (residueImage Λ k) k : ℕ∞) * Module.length A M =
      Module.length Λ M := sorry

end IsLocalRing
