/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Cover

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Crystalline

universe u

namespace CechCrisCover

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
variable (hx₀ : Affine.structureMapCompatible I x₀)
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)

/-- The singleton affine cover of `Spec C` with the polynomial presentation
transported to global sections along `ΓSpecIso`. -/
def ofAffine (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (hx₀ : Affine.structureMapCompatible I x₀)
    (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π) :
    CechCrisCover x₀ where
  Λ := PUnit
  U _ := ⟨⊤, isAffineOpen_top (Spec (.of C))⟩
  coversTop := iSup_const
  h_separated := inferInstance
  vars _ := ι
  π _ := (Scheme.ΓSpecIso (.of C)).inv.hom.comp π.toRingHom
  hπ_comp := sorry
  hπ _ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of C)).inv).surjective.comp hπ

/-- The sole chart of the affine cover is the top open, and its presentation is
the specified polynomial map transported to global sections. -/
theorem ofAffine_spec :
    ((ofAffine x₀ hx₀ π hπ).U PUnit.unit).1 = ⊤ ∧
      (ofAffine x₀ hx₀ π hπ).π PUnit.unit =
        (Scheme.ΓSpecIso (.of C)).inv.hom.comp π.toRingHom := sorry

/-- Every simplex intersection of the singleton affine cover is the top open. -/
theorem ofAffine_simplexOpen (n : ℕ)
    (σ : Fin (n + 1) → (ofAffine x₀ hx₀ π hπ).Λ) :
    (ofAffine x₀ hx₀ π hπ).simplexOpen n σ = ⊤ := sorry

end CechCrisCover
