/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Cotangent.Inertia
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Residue-field determinant of ideal inertia

For a maximal ideal `I`, the determinant of the inertia action on `I / I²` maps canonically from
`(A ⧸ I)ˣ` to the units of `I.ResidueField`.  This leaf keeps that comparison independent of any
discrete valuation or Galois-extension hypotheses.
@stack 09EE
-/

universe u v

namespace Ideal.Cotangent

variable {A : Type u} [CommRing A]
variable {G : Type v} [Group G] [MulSemiringAction G A]

/-- The determinant of ideal inertia, viewed in the units of the residue field. -/
@[stacks 09EE "residue-field determinant of ideal inertia"]
noncomputable def residueDet (I : Ideal A) [I.IsMaximal] :
    I.inertia G →* I.ResidueFieldˣ :=
  (Units.map (Ideal.ResidueField.quotientAlgEquiv (K := ℤ) I).toMonoidHom).comp
    (inertiaDet I)

/-- Evaluation of the residue-field determinant character. -/
@[simp, stacks 09EE "residue-field inertia determinant evaluation"]
theorem residueDet_apply (I : Ideal A) [I.IsMaximal] (σ : I.inertia G) :
    residueDet I σ =
      Units.map (Ideal.ResidueField.quotientAlgEquiv (K := ℤ) I).toMonoidHom
        (inertiaDet I σ) := sorry

/-- The tame-inertia determinant, viewed in the units of the residue field. -/
@[stacks 09EE "residue-field determinant of tame inertia"]
noncomputable def tameResidueDet (I : Ideal A) [I.IsMaximal] :
    I.tameInertia G →* I.ResidueFieldˣ :=
  (Units.map (Ideal.ResidueField.quotientAlgEquiv (K := ℤ) I).toMonoidHom).comp
    (tameInertiaDet I)

/-- On an inertia class, the tame residue determinant is the residue determinant. -/
@[simp, stacks 09EE "tame residue determinant on quotient classes"]
theorem tameResidueDet_mk (I : Ideal A) [I.IsMaximal] (σ : I.inertia G) :
    tameResidueDet I
        ((QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))) σ) =
      residueDet I σ := sorry

/-- Restrict the residue-field determinant to `n`th roots of unity once its power relation is
known. -/
@[stacks 09EE "residue-field inertia determinant in roots of unity"]
noncomputable def residueDetRoots (I : Ideal A) [I.IsMaximal] (n : ℕ)
    (hpow : ∀ σ : I.inertia G, residueDet I σ ∈ rootsOfUnity n I.ResidueField) :
    I.inertia G →* rootsOfUnity n I.ResidueField :=
  MonoidHom.codRestrict (residueDet I) (rootsOfUnity n I.ResidueField) hpow

/-- The roots-of-unity restriction retains the underlying residue-field determinant. -/
@[simp, stacks 09EE "residue-field determinant roots evaluation"]
theorem residueDetRoots_apply (I : Ideal A) [I.IsMaximal] (n : ℕ)
    (hpow : ∀ σ : I.inertia G, residueDet I σ ∈ rootsOfUnity n I.ResidueField)
    (σ : I.inertia G) :
    residueDetRoots I n hpow σ = ⟨residueDet I σ, hpow σ⟩ := sorry

/-- Restrict the tame residue determinant to `n`th roots of unity once its power relation is
known. -/
@[stacks 09EE "tame residue determinant in roots of unity"]
noncomputable def tameResidueDetRoots (I : Ideal A) [I.IsMaximal] (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameResidueDet I τ ∈ rootsOfUnity n I.ResidueField) :
    I.tameInertia G →* rootsOfUnity n I.ResidueField :=
  MonoidHom.codRestrict (tameResidueDet I) (rootsOfUnity n I.ResidueField) hpow

/-- The tame roots-of-unity restriction retains the underlying residue-field determinant. -/
@[simp, stacks 09EE "tame residue determinant roots evaluation"]
theorem tameResidueDetRoots_apply (I : Ideal A) [I.IsMaximal] (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameResidueDet I τ ∈ rootsOfUnity n I.ResidueField)
    (τ : I.tameInertia G) :
    tameResidueDetRoots I n hpow τ = ⟨tameResidueDet I τ, hpow τ⟩ := sorry

/-- On an inertia class, the roots-valued tame determinant has the original residue determinant
as its underlying unit. -/
@[simp, stacks 09EE "tame residue determinant roots on quotient classes"]
theorem tameResidueDetRoots_mk (I : Ideal A) [I.IsMaximal] (n : ℕ)
    (hpow : ∀ τ : I.tameInertia G, tameResidueDet I τ ∈ rootsOfUnity n I.ResidueField)
    (σ : I.inertia G) :
    (tameResidueDetRoots I n hpow
        ((QuotientGroup.mk' ((I.wildInertia G).subgroupOf (I.inertia G))) σ) :
      I.ResidueFieldˣ) = residueDet I σ := sorry

end Ideal.Cotangent
