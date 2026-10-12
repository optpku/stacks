/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.Ideal.Tensor
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Ideals and quotients of completed principal localizations

For an adic Noetherian topological ring, a prime ideal extends to a prime ideal
in the completed principal localization at an element that is a unit modulo
the ideal. Tensor products, completed localized modules, and residue quotients
give canonical descriptions of this extended ideal and its quotient.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace completedPrincipalLocalization

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- A prime ideal remains prime in the completed principal localization at an
element that is a unit modulo the ideal. -/
instance map_isPrime (I : Ideal A) [hI : Fact (IsAdic I)] (p : Ideal A) [p.IsPrime]
    (f : A) [hf : Fact (IsUnit (Ideal.Quotient.mk p f))] :
    (p.map (algebraMap A (completedPrincipalLocalization I f))).IsPrime :=
  sorry

/-- The tensor product of a prime ideal with the completed principal localization
is linearly equivalent to the extended ideal when the localized element is a
unit modulo the prime ideal. -/
def map_ofTensor_linearEquiv (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    p ⊗[A] completedPrincipalLocalization I f ≃ₗ[A]
      (p.map (algebraMap A (completedPrincipalLocalization I f))).restrictScalars A :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict
      ((p.map (algebraMap A (completedPrincipalLocalization I f))).restrictScalars A)
      (p.tensorMul (completedPrincipalLocalization I f))
      (fun _ ↦ sorry))
    sorry

/-- The tensor comparison sends a pure tensor to multiplication by the image of
its ideal element in the completed principal localization. -/
theorem map_ofTensor_linearEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : A) (hx : x ∈ p) (b : completedPrincipalLocalization I f) :
    (map_ofTensor_linearEquiv I hI p f hf (⟨x, hx⟩ ⊗ₜ b)).1 = x • b := sorry

/-- The adic completion of the localized prime ideal is linearly equivalent to
the extended ideal in the completed principal localization when the localized
element is a unit modulo the prime ideal. -/
def localizedCompletion_linearEquiv (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    AdicCompletion (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.Away f p) ≃ₗ[completedPrincipalLocalization I f]
      p.map (algebraMap A (completedPrincipalLocalization I f)) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict
      (p.map (algebraMap A (completedPrincipalLocalization I f)))
      (AdicCompletion.map (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.map (Submonoid.powers f) p.subtype))
      (fun _ ↦ sorry))
    sorry

/-- The completion comparison acts by completing the localized inclusion of the
prime ideal into the base ring. -/
theorem localizedCompletion_linearEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : AdicCompletion (I.map (algebraMap A (Localization.Away f)))
      (LocalizedModule.Away f p)) :
    (localizedCompletion_linearEquiv I hI p f hf x).1 =
      AdicCompletion.map (I.map (algebraMap A (Localization.Away f)))
        (LocalizedModule.map (Submonoid.powers f) p.subtype) x := sorry

/-- The residue quotient by a prime ideal is algebraically equivalent to the
quotient by its extension in the completed principal localization at an element
that is a unit modulo the ideal. -/
def quotient_algEquiv (I : Ideal A) (hI : IsAdic I) (p : Ideal A) [p.IsPrime]
    (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) ≃ₐ[A]
      completedPrincipalLocalization I f ⧸
        p.map (algebraMap A (completedPrincipalLocalization I f)) :=
  AlgEquiv.ofBijective
    (Ideal.quotientMapₐ
      (p.map (algebraMap A (completedPrincipalLocalization I f)))
      (Algebra.ofId A (completedPrincipalLocalization I f))
      Ideal.le_comap_map)
    sorry

/-- The quotient comparison sends a residue class to the class of its canonical
image in the completed principal localization. -/
theorem quotient_algEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) (a : A) :
    quotient_algEquiv I hI p f hf (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk (p.map (algebraMap A (completedPrincipalLocalization I f)))
        (algebraMap A (completedPrincipalLocalization I f) a) := sorry

/-- The residue quotient by a prime ideal is algebraically equivalent to its
tensor product with the completed principal localization at an element that is
a unit modulo the ideal. -/
def quotient_tensor_algEquiv (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f)) :
    (A ⧸ p) ≃ₐ[A]
      (A ⧸ p) ⊗[A] completedPrincipalLocalization I f :=
  AlgEquiv.ofBijective
    (Algebra.TensorProduct.includeLeft :
      (A ⧸ p) →ₐ[A]
        (A ⧸ p) ⊗[A] completedPrincipalLocalization I f)
    sorry

/-- The quotient tensor comparison sends a residue class `x` to `x ⊗ₜ 1`. -/
theorem quotient_tensor_algEquiv_apply (I : Ideal A) (hI : IsAdic I)
    (p : Ideal A) [p.IsPrime] (f : A) (hf : IsUnit (Ideal.Quotient.mk p f))
    (x : A ⧸ p) :
    quotient_tensor_algEquiv I hI p f hf x = x ⊗ₜ (1 : completedPrincipalLocalization I f) :=
  sorry

end completedPrincipalLocalization
