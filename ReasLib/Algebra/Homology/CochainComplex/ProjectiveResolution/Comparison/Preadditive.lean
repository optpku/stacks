/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Comparison

/-!
# Additive Homotopy Maps of Projective Resolutions

The canonical homotopy map between projective resolutions is additive in the morphism between the
base complexes.  This leaf packages that operation as an additive homomorphism and exposes its
basic arithmetic computations without introducing a chosen derived category.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.ProjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The canonical projective-resolution lift is an additive homomorphism in the morphism being
lifted. -/
@[stacks 0648 "additive lift through a projective resolution"]
noncomputable def homotopyLiftAddHom {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) →+
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex) :=
  (comparisonAddEquiv P Q).symm.toAddMonoidHom

/-- Evaluating the additive lift homomorphism gives the canonical lift. -/
@[simp]
theorem homotopyLiftAddHom_apply {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (f : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    homotopyLiftAddHom P Q f = P.homotopyLift Q f := by
  rfl

/-- The canonical lift preserves zero. -/
@[simp]
theorem homotopyLift_zero {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    P.homotopyLift Q (0 :
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) = 0 := by
  apply (comparisonEquiv P Q).injective
  change P.homotopyLift Q 0 ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map Q.π =
    0 ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map Q.π
  rw [Limits.zero_comp]
  exact (comparisonEquiv P Q).apply_symm_apply 0

/-- The canonical lift preserves addition. -/
@[simp]
theorem homotopyLift_add {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (f g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyLift Q (f + g) = P.homotopyLift Q f + P.homotopyLift Q g := by
  apply (comparisonEquiv P Q).injective
  change P.homotopyLift Q (f + g) ≫ _ =
    (P.homotopyLift Q f + P.homotopyLift Q g) ≫ _
  rw [Preadditive.add_comp]
  exact ((comparisonEquiv P Q).apply_symm_apply (f + g)).trans
    (congrArg₂ (· + ·) ((comparisonEquiv P Q).apply_symm_apply f)
      ((comparisonEquiv P Q).apply_symm_apply g)).symm

/-- The canonical lift preserves negation. -/
@[simp]
theorem homotopyLift_neg {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (f : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyLift Q (-f) = -P.homotopyLift Q f := by
  apply (comparisonEquiv P Q).injective
  change P.homotopyLift Q (-f) ≫ _ = (-P.homotopyLift Q f) ≫ _
  rw [Preadditive.neg_comp]
  exact ((comparisonEquiv P Q).apply_symm_apply (-f)).trans
    (congrArg Neg.neg ((comparisonEquiv P Q).apply_symm_apply f)).symm

/-- The canonical lift preserves subtraction. -/
@[simp]
theorem homotopyLift_sub {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (f g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyLift Q (f - g) = P.homotopyLift Q f - P.homotopyLift Q g := by
  simp only [sub_eq_add_neg, homotopyLift_add, homotopyLift_neg]

/-- The canonical projective-resolution homotopy map over the zero base morphism is zero. -/
@[simp]
theorem homotopyMap_zero {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    P.homotopyMap Q
        (0 : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) =
      0 := by
  simp only [homotopyMap, Limits.comp_zero, homotopyLift_zero]

/-- Canonical projective-resolution homotopy maps preserve addition of base morphisms. -/
@[simp]
theorem homotopyMap_add {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyMap Q (u + v) = P.homotopyMap Q u + P.homotopyMap Q v := by
  simp only [homotopyMap, Preadditive.comp_add, homotopyLift_add]

/-- Canonical homotopy maps between fixed projective resolutions form an additive homomorphism
in the morphism between the base complexes. -/
@[stacks 0648 "additive canonical homotopy maps of projective resolutions"]
noncomputable def homotopyMapAddHom {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L) :
    ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) →+
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex) :=
  (homotopyLiftAddHom P Q).comp
    (Preadditive.leftComp _
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map P.π))

/-- Evaluating `homotopyMapAddHom` gives the canonical projective-resolution homotopy map. -/
@[simp]
theorem homotopyMapAddHom_apply {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    homotopyMapAddHom P Q u = P.homotopyMap Q u := by
  rfl

/-- Canonical projective-resolution homotopy maps preserve negation of base morphisms. -/
@[simp]
theorem homotopyMap_neg {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyMap Q (-u) = -P.homotopyMap Q u := by
  simp only [homotopyMap, Preadditive.comp_neg, homotopyLift_neg]

/-- Canonical projective-resolution homotopy maps preserve subtraction of base morphisms. -/
@[simp]
theorem homotopyMap_sub {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyMap Q (u - v) = P.homotopyMap Q u - P.homotopyMap Q v := by
  simp only [homotopyMap, Preadditive.comp_sub, homotopyLift_sub]

end CochainComplex.ProjectiveResolution
