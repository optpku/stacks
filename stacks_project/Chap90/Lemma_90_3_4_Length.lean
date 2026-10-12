/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Length.ResidueImage

/-!
# Compatibility checks for residue-image length comparison

This source-facing module retains the previously exposed residue-image API while its
declarations are owned by `ReasLib.RingTheory.LocalRing.Length.ResidueImage`.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Algebra

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

#check (residueImage Λ k : Type u)

section Integral

variable [Algebra.IsIntegral Λ k]

#check (residueImage.instIsMaximal : (RingHom.ker (algebraMap Λ k)).IsMaximal)
#check (residueImage.instField : Field (residueImage Λ k))
#check (residueImage.instAlgebra : Algebra (residueImage Λ k) k)
#check (residueImage.instIsScalarTower : IsScalarTower Λ (residueImage Λ k) k)

end Integral

section Finite

variable [Module.Finite Λ k]

#check (residueImage.instFinite : Module.Finite (residueImage Λ k) k)
#check (Module.length_eq_finrank (residueImage Λ k) k :
  Module.length (residueImage Λ k) k = Module.finrank (residueImage Λ k) k)

end Finite

#check (residueImage.algebraMap_surjective :
  Function.Surjective (algebraMap Λ (residueImage Λ k)))

#check (residueImage.algEquivOfSurjective :
  Function.Surjective (algebraMap Λ k) → residueImage Λ k ≃ₐ[Λ] k)

#check (residueImage.algEquivOfSurjective_mk :
  ∀ (hsurj : Function.Surjective (algebraMap Λ k)) (x : Λ),
    residueImage.algEquivOfSurjective hsurj
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = algebraMap Λ k x)

section Local

variable [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] [Algebra.IsIntegral Λ k]

#check (residueImage.equivResidueField : residueImage Λ k ≃ₐ[Λ] ResidueField Λ)
#check (residueImage.equivResidueField_mk :
  ∀ x : Λ, residueImage.equivResidueField
    (Ideal.Quotient.mk (RingHom.ker (algebraMap Λ k)) x) = residue Λ x)

end Local

end Algebra

namespace IsLocalRing

open Algebra

#check (length_eq_mul_length_residueImage :
  ∀ {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Algebra.IsIntegral Λ (ResidueField A)],
    Module.length Λ M = Module.length A M *
      Module.length (residueImage Λ (ResidueField A)) (ResidueField A))

#check (length_eq_mul_finrank_residueImage :
  ∀ {Λ : Type u} {A : Type v} {M : Type w}
    [CommRing Λ] [CommRing A] [IsLocalRing A] [Algebra Λ A]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M]
    [Module.Finite Λ (ResidueField A)],
    Module.length Λ M = Module.length A M *
      (Module.finrank (residueImage Λ (ResidueField A)) (ResidueField A) : ℕ∞))

end IsLocalRing
