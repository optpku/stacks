/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Comparison

/-!
# Additive Homotopy Maps of Injective Resolutions

The canonical comparison map between injective resolutions is additive in the
map between the resolved complexes.  This file packages that fact as an
`AddMonoidHom` and exposes the standard additive computation API.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.InjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The canonical injective-resolution extension is an additive homomorphism in the morphism
being extended. -/
@[stacks 013Y "additive extension across an injective resolution"]
noncomputable def homotopyExtensionAddHom {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L) :
    ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) →+
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :=
  (comparisonAddEquiv I J).symm.toAddMonoidHom

/-- Evaluating the additive extension homomorphism gives the canonical extension. -/
@[simp]
theorem homotopyExtensionAddHom_apply {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :
    homotopyExtensionAddHom I J g = I.homotopyExtension J g := sorry

/-- The canonical extension preserves zero. -/
@[simp]
theorem homotopyExtension_zero {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L) :
    I.homotopyExtension J (0 :
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) = 0 := sorry

/-- The canonical extension preserves addition. -/
@[simp]
theorem homotopyExtension_add {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (g h : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :
    I.homotopyExtension J (g + h) =
      I.homotopyExtension J g + I.homotopyExtension J h := sorry

/-- The canonical extension preserves negation. -/
@[simp]
theorem homotopyExtension_neg {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :
    I.homotopyExtension J (-g) = -I.homotopyExtension J g := sorry

/-- The canonical extension preserves subtraction. -/
@[simp]
theorem homotopyExtension_sub {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (g h : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :
    I.homotopyExtension J (g - h) =
      I.homotopyExtension J g - I.homotopyExtension J h := sorry

/-- The canonical comparison construction sends the zero map to zero. -/
@[simp]
theorem homotopyMap_zero {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L) :
    I.homotopyMap J
        (0 : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) = 0 := sorry

/-- The canonical comparison construction preserves addition. -/
@[simp]
theorem homotopyMap_add {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (u v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    I.homotopyMap J (u + v) = I.homotopyMap J u + I.homotopyMap J v := sorry

/-- `homotopyMapAddHom I J` is the additive comparison-map construction
between the hom groups of the homotopy category. -/
@[stacks 013Y "Additivity of comparison maps between injective resolutions"]
noncomputable def homotopyMapAddHom {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L) :
    ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) →+
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ⟶
        (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :=
  (homotopyExtensionAddHom I J).comp
    (Preadditive.rightComp _
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map J.ι))

/-- Evaluation of the additive comparison-map construction is the canonical
comparison map. -/
@[simp]
theorem homotopyMapAddHom_apply {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    homotopyMapAddHom I J u = I.homotopyMap J u := sorry

/-- The canonical comparison construction preserves additive inverses. -/
@[simp]
theorem homotopyMap_neg {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    I.homotopyMap J (-u) = -I.homotopyMap J u := sorry

/-- The canonical comparison construction preserves subtraction. -/
@[simp]
theorem homotopyMap_sub {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (u v : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    I.homotopyMap J (u - v) = I.homotopyMap J u - I.homotopyMap J v := sorry

end CochainComplex.InjectiveResolution


