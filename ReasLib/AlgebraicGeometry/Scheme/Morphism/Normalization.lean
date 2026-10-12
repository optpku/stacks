/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Universal property of relative normalization

This file packages the universal property of relative normalization for factorizations through
integral morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The relative normalization of a quasi-compact and quasi-separated morphism is initial among
its factorizations through an integral morphism. -/
theorem existsUnique_lift_fromNormalization
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π) :
    ∃! h : f.normalization ⟶ Z,
      f.toNormalization ≫ h = g ∧ h ≫ π = f.fromNormalization := sorry

/-- An integral intermediate factor of a relative normalization has the corresponding universal
property for every further integral factorization. -/
theorem existsUnique_lift_normalizationDesc
    {X Y Z Z' : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π] (hf : f = g ≫ π)
    (g' : Y ⟶ Z') (π' : Z' ⟶ Z) [IsIntegralHom π'] (hg : g = g' ≫ π') :
    ∃! h' : f.normalization ⟶ Z',
      f.toNormalization ≫ h' = g' ∧ h' ≫ π' = f.normalizationDesc g π hf := sorry

/-- A commutative square of quasi-compact and quasi-separated morphisms induces a unique
morphism between their relative normalizations compatible with both canonical factorizations. -/
theorem existsUnique_map_between_normalizations
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (f₁ : Y₁ ⟶ X₁) [QuasiCompact f₁] [QuasiSeparated f₁]
    (f₂ : Y₂ ⟶ X₂) [QuasiCompact f₂] [QuasiSeparated f₂]
    (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁)
    (comm : gY ≫ f₁ = f₂ ≫ gX) :
    ∃! h : f₂.normalization ⟶ f₁.normalization,
      f₂.toNormalization ≫ h = gY ≫ f₁.toNormalization ∧
        h ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX := sorry

/-- The canonical morphism from the relative normalization of a normalization to the original
normalization is an isomorphism. -/
instance isIso_fromNormalization_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    IsIso ((f.toNormalization).fromNormalization) := sorry

end AlgebraicGeometry.Scheme.Hom
