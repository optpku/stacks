/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Inertia

@[expose] public section

/-!
# Cotangent representation of ideal inertia

For an ideal `I` preserved by an algebra action, inertia acts on `I.Cotangent = I / I²`.
The quotient-linear compatibility is recorded separately from the underlying transport so that
the latter can be reused over any smaller scalar ring.
@stack 09EE
-/

universe u v

namespace Ideal.Cotangent

variable {A : Type u}
variable [CommRing A]
variable {G : Type*} [Group G] [MulSemiringAction G A]

/-- The explicit map on `I / I²` induced by an inertia element. -/
@[stacks 09EE "inertia map on the cotangent module"]
noncomputable def inertiaMap (I : Ideal A) (σ : I.inertia G) :
    I.Cotangent →ₗ[ℤ] I.Cotangent :=
  Ideal.mapCotangent I I (MulSemiringAction.toAlgEquiv ℤ A (σ : G)).toAlgHom
    fun x hx ↦ Ideal.smul_mem_of_mem_inertia I σ ⟨x, hx⟩

/-- The inertia map sends a cotangent generator to the class of its image under the ambient
action. -/
@[simp, stacks 09EE "inertia map on cotangent generators"]
theorem inertiaMap_toCotangent (I : Ideal A) (σ : I.inertia G) (x : I) :
    inertiaMap I σ (I.toCotangent x) =
      I.toCotangent
        ⟨(σ : G) • (x : A), Ideal.smul_mem_of_mem_inertia I σ x⟩ := sorry

/-- Applying the cotangent map for `σ` after the one for `σ⁻¹` is the identity. -/
@[stacks 09EE "inverse law for inertia cotangent maps"]
theorem inertiaMap_comp_inv (I : Ideal A) (σ : I.inertia G) :
    (inertiaMap I σ).comp (inertiaMap I σ⁻¹) =
      LinearMap.id := sorry

/-- Applying the cotangent map for `σ⁻¹` after the one for `σ` is the identity. -/
@[stacks 09EE "inverse law for inertia cotangent maps"]
theorem inertiaMap_inv_comp (I : Ideal A) (σ : I.inertia G) :
    (inertiaMap I σ⁻¹).comp (inertiaMap I σ) =
      LinearMap.id := sorry

/-- The `ℤ`-linear cotangent equivalence induced by an inertia element. -/
@[stacks 09EE "integral-linear inertia action on the cotangent module"]
noncomputable def inertiaLinearEquiv (I : Ideal A) (σ : I.inertia G) :
    I.Cotangent ≃ₗ[ℤ] I.Cotangent :=
  LinearEquiv.ofLinear (inertiaMap I σ) (inertiaMap I σ⁻¹)
    (inertiaMap_comp_inv I σ) (inertiaMap_inv_comp I σ)

/-- The additive cotangent transport induced by an inertia element. -/
@[stacks 09EE "additive inertia action on the cotangent module"]
noncomputable def inertiaAddEquiv (I : Ideal A) (σ : I.inertia G) :
    I.Cotangent ≃+ I.Cotangent :=
  (inertiaLinearEquiv I σ).toAddEquiv

/-- The additive cotangent transport of inertia is linear over the quotient ring. -/
@[stacks 09EE "quotient linearity of the inertia cotangent action"]
theorem inertiaAddEquiv_smul (I : Ideal A) (σ : I.inertia G)
    (r : A ⧸ I) (x : I.Cotangent) :
    inertiaAddEquiv I σ (r • x) = r • inertiaAddEquiv I σ x := sorry

/-- The cotangent equivalence attached to an inertia element. -/
@[stacks 09EE "inertia action on the cotangent module"]
noncomputable def inertiaEquiv (I : Ideal A) (σ : I.inertia G) :
    I.Cotangent ≃ₗ[A ⧸ I] I.Cotangent :=
  (inertiaAddEquiv I σ).toLinearEquiv (inertiaAddEquiv_smul I σ)

/-- Evaluation of the inertia representation on a cotangent class. -/
@[simp, stacks 09EE "inertia cotangent action formula"]
theorem inertiaEquiv_apply (I : Ideal A) (σ : I.inertia G) (x : I.Cotangent) :
    inertiaEquiv I σ x = inertiaAddEquiv I σ x := sorry

/-- On a cotangent generator, inertia acts by applying the ambient automorphism to its
representative. -/
@[simp, stacks 09EE "inertia cotangent action on generators"]
theorem inertiaEquiv_toCotangent (I : Ideal A) (σ : I.inertia G) (x : I) :
    inertiaEquiv I σ (I.toCotangent x) =
      I.toCotangent
        ⟨(σ : G) • (x : A), Ideal.smul_mem_of_mem_inertia I σ x⟩ := sorry

/-- The identity inertia element acts trivially on the cotangent module. -/
@[stacks 09EE "identity law for the inertia cotangent action"]
theorem inertiaEquiv_one (I : Ideal A) :
    inertiaEquiv I (1 : I.inertia G) = 1 := sorry

/-- Multiplication in inertia corresponds to composition on the cotangent module. -/
@[stacks 09EE "multiplication law for the inertia cotangent action"]
theorem inertiaEquiv_mul (I : Ideal A) (σ τ : I.inertia G) :
    inertiaEquiv I (σ * τ) = inertiaEquiv I σ * inertiaEquiv I τ := sorry

/-- The multiplicative representation of inertia on the cotangent module. -/
@[stacks 09EE "inertia cotangent representation"]
noncomputable def inertiaRepresentation (I : Ideal A) :
    I.inertia G →* (I.Cotangent ≃ₗ[A ⧸ I] I.Cotangent) where
  toFun := inertiaEquiv I
  map_one' := inertiaEquiv_one I
  map_mul' := inertiaEquiv_mul I

/-- The inertia representation evaluates to the canonical quotient-linear cotangent action. -/
@[simp, stacks 09EE "inertia representation evaluation"]
theorem inertiaRepresentation_apply (I : Ideal A) (σ : I.inertia G) :
    inertiaRepresentation I σ = inertiaEquiv I σ := sorry

/-- The kernel of the inertia action on the cotangent module is exactly wild inertia. -/
@[stacks 09EE "wild inertia is the cotangent-action kernel"]
theorem inertiaRepresentation_ker (I : Ideal A) :
    (inertiaRepresentation I).ker =
      (I.wildInertia G).subgroupOf (I.inertia G) := sorry

/-- Wild inertia acts trivially on the cotangent module.  This inclusion form is the interface
used to descend the representation through the tame quotient. -/
@[stacks 09EE "wild inertia acts trivially on the cotangent module"]
theorem wildInertia_le_ker_inertiaRepresentation (I : Ideal A) :
    (I.wildInertia G).subgroupOf (I.inertia G) ≤ (inertiaRepresentation I).ker := sorry

/-- The cotangent representation factored through tame inertia. -/
@[stacks 09EE "tame inertia cotangent representation"]
noncomputable def tameInertiaRepresentation (I : Ideal A) :
    I.tameInertia G →* (I.Cotangent ≃ₗ[A ⧸ I] I.Cotangent) :=
  QuotientGroup.lift ((I.wildInertia G).subgroupOf (I.inertia G))
    (inertiaRepresentation I) (wildInertia_le_ker_inertiaRepresentation I)

/-- The tame inertia representation agrees with the inertia representation on quotient
classes. -/
@[simp, stacks 09EE "tame inertia representation on quotient classes"]
theorem tameInertiaRepresentation_mk (I : Ideal A) (σ : I.inertia G) :
    tameInertiaRepresentation I
        ((QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))) σ) =
      inertiaRepresentation I σ := sorry

/-- Determinant character of the cotangent representation, valued in units of `A ⧸ I`. -/
@[stacks 09EE "inertia cotangent determinant"]
noncomputable def inertiaDet (I : Ideal A) :
    I.inertia G →* (A ⧸ I)ˣ :=
    (LinearEquiv.det :
      (I.Cotangent ≃ₗ[A ⧸ I] I.Cotangent) →* (A ⧸ I)ˣ).comp
    (inertiaRepresentation I)

/-- The determinant character evaluates as the determinant of the cotangent action. -/
@[simp, stacks 09EE "inertia determinant evaluation"]
theorem inertiaDet_apply (I : Ideal A) (σ : I.inertia G) :
    inertiaDet I σ = LinearEquiv.det (inertiaEquiv I σ) := sorry

/-- Wild inertia is contained in the kernel of the cotangent determinant character. -/
@[stacks 09EE "wild inertia is killed by the cotangent determinant"]
theorem wildInertia_le_ker_inertiaDet (I : Ideal A) :
    (I.wildInertia G).subgroupOf (I.inertia G) ≤ (inertiaDet I).ker := sorry

/-- The determinant character factored through tame inertia. -/
@[stacks 09EE "tame inertia cotangent determinant"]
noncomputable def tameInertiaDet (I : Ideal A) :
    I.tameInertia G →* (A ⧸ I)ˣ :=
  QuotientGroup.lift ((I.wildInertia G).subgroupOf (I.inertia G))
    (inertiaDet I) (wildInertia_le_ker_inertiaDet I)

/-- The tame inertia determinant agrees with the inertia determinant on quotient classes. -/
@[simp, stacks 09EE "tame inertia determinant on quotient classes"]
theorem tameInertiaDet_mk (I : Ideal A) (σ : I.inertia G) :
    tameInertiaDet I
        ((QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))) σ) =
      inertiaDet I σ := sorry

/-- The tame inertia determinant is the determinant of the tame cotangent representation. -/
@[stacks 09EE "tame inertia determinant representation compatibility"]
theorem tameInertiaDet_eq (I : Ideal A) :
    tameInertiaDet (G := G) I =
      (LinearEquiv.det :
        (I.Cotangent ≃ₗ[A ⧸ I] I.Cotangent) →* (A ⧸ I)ˣ).comp
        (tameInertiaRepresentation (G := G) I) := sorry

/-- Restrict the determinant to roots of unity once the relevant power relation is available. -/
@[stacks 09EE "inertia determinant roots of unity restriction"]
noncomputable def inertiaDetRoots (I : Ideal A) (n : ℕ)
    (hpow : ∀ σ : I.inertia G, inertiaDet I σ ∈ rootsOfUnity n (A ⧸ I)) :
    I.inertia G →* rootsOfUnity n (A ⧸ I) :=
  MonoidHom.codRestrict (inertiaDet I) (rootsOfUnity n (A ⧸ I)) hpow

/-- The roots-of-unity restriction retains the underlying determinant value. -/
@[simp, stacks 09EE "inertia determinant roots evaluation"]
theorem inertiaDetRoots_apply (I : Ideal A) (n : ℕ)
    (hpow : ∀ σ : I.inertia G, inertiaDet I σ ∈ rootsOfUnity n (A ⧸ I))
    (σ : I.inertia G) :
    inertiaDetRoots I n hpow σ =
      ⟨inertiaDet I σ, hpow σ⟩ := sorry

/-- Restrict the tame inertia determinant to roots of unity once the relevant power relation is
available. -/
@[stacks 09EE "tame inertia determinant roots of unity restriction"]
noncomputable def tameInertiaDetRoots (I : Ideal A) (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameInertiaDet I τ ∈ rootsOfUnity n (A ⧸ I)) :
    I.tameInertia G →* rootsOfUnity n (A ⧸ I) :=
  MonoidHom.codRestrict (tameInertiaDet I) (rootsOfUnity n (A ⧸ I)) hpow

/-- The tame roots-of-unity restriction retains the underlying determinant value. -/
@[simp, stacks 09EE "tame inertia determinant roots evaluation"]
theorem tameInertiaDetRoots_apply (I : Ideal A) (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameInertiaDet I τ ∈ rootsOfUnity n (A ⧸ I))
    (τ : I.tameInertia G) :
    tameInertiaDetRoots I n hpow τ =
      ⟨tameInertiaDet I τ, hpow τ⟩ := sorry

/-- On a quotient class, the tame roots-of-unity character has the original inertia
determinant as its underlying unit. -/
@[simp, stacks 09EE "tame inertia roots on quotient classes"]
theorem tameInertiaDetRoots_mk (I : Ideal A) (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameInertiaDet I τ ∈ rootsOfUnity n (A ⧸ I))
    (σ : I.inertia G) :
    ((tameInertiaDetRoots I n hpow
      ((QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))) σ) :
        rootsOfUnity n (A ⧸ I)) : (A ⧸ I)ˣ) = inertiaDet I σ := sorry

end Ideal.Cotangent
