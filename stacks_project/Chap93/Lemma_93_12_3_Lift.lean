module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.RingHom.QuotientLift.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime

/-!
# Flat algebra lifts along nilpotent thickenings

This leaf owns the existence of an `A'`-flat algebra lift of an `A`-algebra, the
syntomic-off-`V(I)` hypothesis, and the comparison of flat lifts with
`b`-adic completion.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v

namespace Algebra.NilpotentLift

/-- Existence of an `A'`-flat algebra `B'` together with an `A`-algebra
identification `B' ⊗[A'] A ≃ₐ[A] B`. -/
def existsFlatLift (A' : Type u) [CommRing A'] (A : Type u) [CommRing A]
    [Algebra A' A] (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A' B'),
    Module.Flat A' B' ∧ Nonempty ((B' ⊗[A'] A) ≃ₐ[A] B)

/-- Unfolding of `existsFlatLift`. -/
theorem existsFlatLift_iff (A' : Type u) [CommRing A'] (A : Type u) [CommRing A]
    [Algebra A' A] (B : Type u) [CommRing B] [Algebra A B] :
    existsFlatLift A' A B ↔
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra A' B'),
        Module.Flat A' B' ∧ Nonempty ((B' ⊗[A'] A) ≃ₐ[A] B) :=
  sorry

/-- If `A' → A` is surjective, a flat algebra lift exists if and only if there is
a `RingHom.QuotientLift` of `B` along `algebraMap A' A` whose upstairs algebra
is `A'`-flat. -/
theorem existsFlatLift_iff_quotientLift (A' : Type u) [CommRing A'] (A : Type u)
    [CommRing A] [Algebra A' A] (B : Type u) [CommRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A' A)) :
    existsFlatLift A' A B ↔
      ∃ L : RingHom.QuotientLift.{u, u, u, u} (algebraMap A' A) B,
        Module.Flat A' L.upstairs :=
  sorry

end Algebra.NilpotentLift

namespace RingHom

/-- A ring homomorphism is syntomic on the complement of `V(I)` if it is
syntomic at every prime of the target outside `PrimeSpectrum.zeroLocus I`. -/
def SyntomicOnComplement {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) : Prop :=
  ∀ q : PrimeSpectrum S, q ∉ PrimeSpectrum.zeroLocus I → f.SyntomicAtPrime q

namespace SyntomicOnComplement

/-- Syntomicity on the complement of `V(I)` is equivalent to syntomicity of
`R → S_g` for every `g ∈ I`. -/
theorem iff_forall_away {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) :
    f.SyntomicOnComplement I ↔
      ∀ g ∈ I, ((algebraMap S (Localization.Away g)).comp f).Syntomic :=
  sorry

end SyntomicOnComplement

end RingHom

namespace Algebra.NilpotentLift

/-- For a surjection of Noetherian rings with nilpotent kernel, a finite-type
flat algebra, and an ideal on whose complement the algebra map is syntomic, a
flat lift exists if and only if the adic completion admits a flat lift. -/
theorem existsFlatLift_iff_existsFlatLift_adicCompletion
    {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Flat A B]
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) (hsyn : (algebraMap A B).SyntomicOnComplement b) :
    existsFlatLift A' A B ↔ existsFlatLift A' A (AdicCompletion b B) :=
  sorry

end Algebra.NilpotentLift

end
