/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import stacks_project.Chap105.Lemma_105_6_1_Moduli
public import stacks_project.Chap105.Remark_105_6_2_Quotient
public import stacks_project.Chap105.Remark_105_6_2_Weierstrass

/-!
# Remark 105.6.2

The Weierstrass-cover argument of Lemma 105.6.1 shows that the moduli stack of
elliptic curves equals the quotient stack `[W / H]`, and is therefore a global
quotient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient
open AlgebraicSpace FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

/-- The map of Weierstrass coefficient indices `a₁, a₂, a₃, a₄, a₆` toward the
classifying Weierstrass scheme. -/
def coeffToScheme (c : Coeff) : WeierstrassScheme.Coeff :=
  match c with
  | Coeff.a1 => WeierstrassScheme.Coeff.a1
  | Coeff.a2 => WeierstrassScheme.Coeff.a2
  | Coeff.a3 => WeierstrassScheme.Coeff.a3
  | Coeff.a4 => WeierstrassScheme.Coeff.a4
  | Coeff.a6 => WeierstrassScheme.Coeff.a6

/-- `coeffToScheme` sends `a₁` to `a₁`. -/
theorem coeffToScheme_a1 : coeffToScheme .a1 = WeierstrassScheme.Coeff.a1 :=
  sorry

/-- The inverse map of Weierstrass coefficient indices `a₁, a₂, a₃, a₄, a₆`. -/
def coeffFromScheme (c : WeierstrassScheme.Coeff) : Coeff :=
  match c with
  | WeierstrassScheme.Coeff.a1 => Coeff.a1
  | WeierstrassScheme.Coeff.a2 => Coeff.a2
  | WeierstrassScheme.Coeff.a3 => Coeff.a3
  | WeierstrassScheme.Coeff.a4 => Coeff.a4
  | WeierstrassScheme.Coeff.a6 => Coeff.a6

/-- `coeffFromScheme` sends `a₁` to `a₁`. -/
theorem coeffFromScheme_a1 : coeffFromScheme .a1 = Coeff.a1 :=
  sorry

/-- The bijection of Weierstrass coefficient indices `a₁, a₂, a₃, a₄, a₆`. -/
def coeffEquiv : Coeff ≃ WeierstrassScheme.Coeff where
  toFun := coeffToScheme
  invFun := coeffFromScheme
  left_inv := sorry
  right_inv := sorry

/-- `coeffEquiv` identifies the two `a₁` indices. -/
theorem coeffEquiv_a1 : coeffEquiv .a1 = WeierstrassScheme.Coeff.a1 :=
  sorry

/-- The polynomial-ring map induced by the coefficient bijection. -/
def coeffRingHom : WeierstrassScheme.coeffRing →+* coeffRing :=
  (MvPolynomial.rename fun x : ULift.{u} WeierstrassScheme.Coeff ↦
    ⟨coeffFromScheme x.down⟩).toRingHom

/-- `coeffRingHom` sends the coordinate `a₁` to the coordinate `a₁`. -/
theorem coeffRingHom_X_a1 :
    coeffRingHom (MvPolynomial.X ⟨.a1⟩) = MvPolynomial.X ⟨.a1⟩ :=
  sorry

/-- Powers of the source discriminant are sent into the inverted target discriminant. -/
theorem coeffRingHom_powers_le :
    Submonoid.powers WeierstrassScheme.Δ ≤
      (Submonoid.powers discriminant).comap coeffRingHom :=
  sorry

/-- The localized coordinate-ring map induced by the Weierstrass coefficient bijection. -/
def ringHom : WeierstrassScheme.ring →+* ring :=
  IsLocalization.map ring coeffRingHom coeffRingHom_powers_le

/-- `ringHom` sends the inverted source discriminant to the inverted target discriminant. -/
theorem ringHom_Δ :
    ringHom (algebraMap _ _ WeierstrassScheme.Δ) = algebraMap _ _ discriminant :=
  sorry

/-- Compatibility of `Spec.map ringHom` with the structure morphisms over `Spec ℤ`. -/
theorem schemeComparison_w :
    Spec.map (CommRingCat.ofHom ringHom) ≫ WeierstrassScheme.overInt.hom = scheme.hom :=
  sorry

/-- The comparison morphism `W ⟶ W` over `Spec ℤ` induced by the coefficient bijection
`a₁, a₂, a₃, a₄, a₆` and localization of `Δ`. -/
def schemeComparison : scheme ⟶ WeierstrassScheme.overInt :=
  Over.homMk (Spec.map (CommRingCat.ofHom ringHom)) schemeComparison_w

/-- `schemeComparison` is the spectrum of `ringHom`, and identifies the two inverted
discriminants. -/
theorem schemeComparison_spec :
    schemeComparison.left = Spec.map (CommRingCat.ofHom ringHom) ∧
      ringHom (algebraMap _ _ WeierstrassScheme.Δ) = algebraMap _ _ discriminant :=
  sorry

/-- The coefficient comparison of Weierstrass schemes is an isomorphism. -/
instance instIsIso_schemeComparison : IsIso schemeComparison :=
  sorry

end AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

namespace AlgebraicGeometry.M11

/-- Remark 105.6.2 (1): The argument sketched in Lemma 105.6.1 shows that the moduli
stack of elliptic curves equals the quotient stack `[W / H]` of the Weierstrass scheme
`W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` by the group scheme `H` of admissible changes of
variables. -/
@[stacks 072U]
theorem equiv_weierstrassQuotient :
    ∃ e : stack ⟶ M11.{u},
      (toBasedFunctor e).IsEquivalence ∧
        Nonempty
          (atlas ≫ e ≅
            toGroupoids.map (ofOverMap schemeComparison) ≫
              (ofOverSliceEquiv WeierstrassScheme.overInt).hom ≫ weierstrassCover.{u}) :=
  sorry

/-- Remark 105.6.2 (2): The moduli stack of elliptic curves is a global quotient stack. -/
@[stacks 072U]
instance instIsGlobalQuotientStack : IsGlobalQuotientStack M11.{u} :=
  sorry

end AlgebraicGeometry.M11
