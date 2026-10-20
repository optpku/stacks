module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.AdicCompletion.Map
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Regular.GRing

/-!
# Étale approximation of maps of adic completions

An `A`-algebra map of `I`-adic completions of finite type algebras over a
G-ring can be approximated modulo a positive power of `I` after an étale
extension of the target that induces the canonical closed-fiber isomorphism.
-/

@[expose] public section

universe u v w x

namespace AdicCompletion.EtaleApprox

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- The stage-`n` extension of `I` in `C` is contained in the comap of the
stage-`n` extension of `I` along an `A`-algebra over `C`. -/
theorem le_comap_extensionPow {C' : Type x} [CommRing C'] [Algebra A C']
    [Algebra C C'] [IsScalarTower A C C'] (I : Ideal A) (n : ℕ) :
    (Ideal.map (algebraMap A C) I) ^ n ≤
      Ideal.comap (IsScalarTower.toAlgHom A C C')
        ((Ideal.map (algebraMap A C') I) ^ n) := sorry

/-- Stage-`N` agreement of a formal `A`-algebra map of `I`-adic completions
with an algebra map into an extension of `C`, after the canonical quotient
comparison `C ⧸ (IC) ^ N ⟶ C' ⧸ (IC') ^ N`. -/
def AgreeModExtensionPow {C' : Type x} [CommRing C'] [Algebra A C']
    [Algebra C C'] [IsScalarTower A C C'] (I : Ideal A) (N : ℕ)
    (ψ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A]
      AdicCompletion (Ideal.map (algebraMap A C) I) C)
    (φ : B →ₐ[A] C') : Prop :=
  ∀ b : B,
    Ideal.quotientMapₐ ((Ideal.map (algebraMap A C') I) ^ N)
        (IsScalarTower.toAlgHom A C C') (le_comap_extensionPow I N)
        (evalₐ (Ideal.map (algebraMap A C) I) N
          (ψ (algebraMap B (AdicCompletion (Ideal.map (algebraMap A B) I) B) b))) =
      Ideal.Quotient.mkₐ A ((Ideal.map (algebraMap A C') I) ^ N) (φ b)

/-- Unfolding of `AgreeModExtensionPow` at an element of the source algebra. -/
theorem agree_apply {C' : Type x} [CommRing C'] [Algebra A C']
    [Algebra C C'] [IsScalarTower A C C'] (I : Ideal A) (N : ℕ)
    (ψ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A]
      AdicCompletion (Ideal.map (algebraMap A C) I) C)
    (φ : B →ₐ[A] C') (h : AgreeModExtensionPow I N ψ φ) (b : B) :
    Ideal.quotientMapₐ ((Ideal.map (algebraMap A C') I) ^ N)
        (IsScalarTower.toAlgHom A C C') (le_comap_extensionPow I N)
        (evalₐ (Ideal.map (algebraMap A C) I) N
          (ψ (algebraMap B (AdicCompletion (Ideal.map (algebraMap A B) I) B) b))) =
      Ideal.Quotient.mkₐ A ((Ideal.map (algebraMap A C') I) ^ N) (φ b) := sorry

/-- Over a G-ring, every `A`-algebra map of `I`-adic completions of finite type
algebras can be approximated modulo `I ^ N` by an algebra map into an étale
extension of the target that induces the canonical closed-fiber isomorphism. -/
theorem exists_of_isGRing [IsGRing A] [Algebra.FiniteType A B]
    [Algebra.FiniteType A C] (I : Ideal A)
    (ψ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A]
      AdicCompletion (Ideal.map (algebraMap A C) I) C)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ (C' : Type (max u v w)) (_ : CommRing C') (_ : Algebra A C')
      (_ : Algebra C C') (_ : IsScalarTower A C C') (_ : Algebra.Etale C C'),
      Function.Bijective
          (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom A C C') I) ∧
        ∃ φ : B →ₐ[A] C', AgreeModExtensionPow I N ψ φ := sorry

/-- The structure map of an `A`-algebra over `C` is adically continuous for
the extended ideals of `I`. -/
theorem adicContinuous_algebraMap {C' : Type x} [CommRing C'] [Algebra A C']
    [Algebra C C'] [IsScalarTower A C C'] (I : Ideal A) :
    (algebraMap C C').AdicContinuous (Ideal.map (algebraMap A C) I)
      (Ideal.map (algebraMap A C') I) := by
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Ideal.map_le_iff_le_comap.mpr
  have containment := le_comap_extensionPow (C := C) (C' := C') I 1
  rw [pow_one, pow_one, ← Ideal.comap_coe, IsScalarTower.coe_toAlgHom] at containment
  exact containment

/-- An étale algebra map inducing an isomorphism modulo `I` induces a
bijective map on `I`-adic completions. -/
theorem completionMap_bijective {C' : Type x} [CommRing C'] [Algebra A C']
    [Algebra C C'] [IsScalarTower A C C'] [Algebra.Etale C C'] (I : Ideal A)
    (hquot : Function.Bijective
      (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom A C C') I)) :
    Function.Bijective
      (RingHom.AdicContinuous.completionMap (adicContinuous_algebraMap I) :
        AdicCompletion (Ideal.map (algebraMap A C) I) C →+*
          AdicCompletion (Ideal.map (algebraMap A C') I) C') := sorry

end AdicCompletion.EtaleApprox
