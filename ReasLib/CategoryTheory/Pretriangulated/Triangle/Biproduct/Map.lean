/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Triangle.Biproduct

@[expose] public section

/-!
# Naturality of Binary Biproducts of Triangles

This leaf contains the componentwise map between binary biproduct triangles and
its computation and naturality interface.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]
  [HasBinaryBiproducts D]

/-- The first square for a componentwise map of binary biproduct triangles. -/
@[reassoc]
theorem biproductTriangle.map_comm₁ {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    (biproductTriangle T₁ T₂).mor₁ ≫ biprod.map φ₁.hom₂ φ₂.hom₂ =
      biprod.map φ₁.hom₁ φ₂.hom₁ ≫ (biproductTriangle S₁ S₂).mor₁ := sorry

/-- The second square for a componentwise map of binary biproduct triangles. -/
@[reassoc]
theorem biproductTriangle.map_comm₂ {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    (biproductTriangle T₁ T₂).mor₂ ≫ biprod.map φ₁.hom₃ φ₂.hom₃ =
      biprod.map φ₁.hom₂ φ₂.hom₂ ≫ (biproductTriangle S₁ S₂).mor₂ := sorry

/-- The third square for a componentwise map of binary biproduct triangles. -/
@[reassoc]
theorem biproductTriangle.map_comm₃ {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    (biproductTriangle T₁ T₂).mor₃ ≫
        (biprod.map φ₁.hom₁ φ₂.hom₁)⟦(1 : ℤ)⟧' =
      biprod.map φ₁.hom₃ φ₂.hom₃ ≫ (biproductTriangle S₁ S₂).mor₃ := sorry

/-- Stacks 05QS: the componentwise map between objectwise binary biproduct triangles. -/
@[stacks 05QS, simps!]
def biproductTriangle.map {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    biproductTriangle T₁ T₂ ⟶ biproductTriangle S₁ S₂ :=
  Triangle.homMk _ _
    (biprod.map φ₁.hom₁ φ₂.hom₁)
    (biprod.map φ₁.hom₂ φ₂.hom₂)
    (biprod.map φ₁.hom₃ φ₂.hom₃)
    (biproductTriangle.map_comm₁ φ₁ φ₂)
    (biproductTriangle.map_comm₂ φ₁ φ₂)
    (biproductTriangle.map_comm₃ φ₁ φ₂)

/-- A componentwise biproduct map preserves the left inclusion. -/
@[simp]
theorem biproductTriangle.inl_map {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    biproductTriangle.inl T₁ T₂ ≫ biproductTriangle.map φ₁ φ₂ =
      φ₁ ≫ biproductTriangle.inl S₁ S₂ := sorry

/-- A componentwise biproduct map preserves the right inclusion. -/
@[simp]
theorem biproductTriangle.inr_map {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    biproductTriangle.inr T₁ T₂ ≫ biproductTriangle.map φ₁ φ₂ =
      φ₂ ≫ biproductTriangle.inr S₁ S₂ := sorry

/-- A componentwise biproduct map preserves the left projection. -/
@[simp]
theorem biproductTriangle.map_fst {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    biproductTriangle.map φ₁ φ₂ ≫ biproductTriangle.fst S₁ S₂ =
      biproductTriangle.fst T₁ T₂ ≫ φ₁ := sorry

/-- A componentwise biproduct map preserves the right projection. -/
@[simp]
theorem biproductTriangle.map_snd {T₁ T₂ S₁ S₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) :
    biproductTriangle.map φ₁ φ₂ ≫ biproductTriangle.snd S₁ S₂ =
      biproductTriangle.snd T₁ T₂ ≫ φ₂ := sorry

/-- The componentwise binary biproduct map of identity triangle morphisms is the identity. -/
@[simp]
theorem biproductTriangle.map_id (T₁ T₂ : Triangle D) :
    biproductTriangle.map (𝟙 T₁) (𝟙 T₂) = 𝟙 (biproductTriangle T₁ T₂) := sorry

/-- Componentwise binary biproduct maps respect composition. -/
@[simp]
theorem biproductTriangle.map_comp {T₁ T₂ S₁ S₂ U₁ U₂ : Triangle D}
    (φ₁ : T₁ ⟶ S₁) (φ₂ : T₂ ⟶ S₂) (ψ₁ : S₁ ⟶ U₁) (ψ₂ : S₂ ⟶ U₂) :
    biproductTriangle.map (φ₁ ≫ ψ₁) (φ₂ ≫ ψ₂) =
      biproductTriangle.map φ₁ φ₂ ≫ biproductTriangle.map ψ₁ ψ₂ := sorry

end CategoryTheory.Pretriangulated
