/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.Triangle

@[expose] public section

/-!
# Comparing Lifted and Ambient Triangles

A triangle whose vertices satisfy a shift-stable object property can be lifted to the full
subcategory.  Mapping that lift back along the inclusion recovers the original ambient triangle
through a canonical natural isomorphism which is the identity at every vertex.
-/

noncomputable section

universe v u

namespace CategoryTheory

open ObjectProperty Pretriangulated

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

namespace ObjectProperty.triangle

variable (P : ObjectProperty C)

/-- The first square needed for the comparison between a lifted triangle and its ambient
triangle. -/
theorem lift.inclusionIso.app_comm₁ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift P ⋙ P.ι.mapTriangle).obj T).mor₁ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (P.triangle.ι.obj T).mor₁ := sorry

/-- The second square needed for the comparison between a lifted triangle and its ambient
triangle. -/
theorem lift.inclusionIso.app_comm₂ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift P ⋙ P.ι.mapTriangle).obj T).mor₂ ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ (P.triangle.ι.obj T).mor₂ := sorry

/-- The connecting square needed for the comparison between a lifted triangle and its ambient
triangle. -/
theorem lift.inclusionIso.app_comm₃ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift P ⋙ P.ι.mapTriangle).obj T).mor₃ ≫ (Iso.refl _).hom⟦(1 : ℤ)⟧' =
      (Iso.refl _).hom ≫ (P.triangle.ι.obj T).mor₃ := sorry

/-- The componentwise comparison between a lifted triangle mapped back to `C` and its original
ambient triangle. -/
noncomputable def lift.inclusionIso.app [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    (lift P ⋙ P.ι.mapTriangle).obj T ≅ P.triangle.ι.obj T :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (lift.inclusionIso.app_comm₁ P T)
    (lift.inclusionIso.app_comm₂ P T)
    (lift.inclusionIso.app_comm₃ P T)

/-- The forward comparison is the identity at the first vertex. -/
@[simp]
theorem lift.inclusionIso.app_hom₁ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).hom).hom₁ = 𝟙 T.obj.obj₁ := sorry

/-- The forward comparison is the identity at the second vertex. -/
@[simp]
theorem lift.inclusionIso.app_hom₂ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).hom).hom₂ = 𝟙 T.obj.obj₂ := sorry

/-- The forward comparison is the identity at the third vertex. -/
@[simp]
theorem lift.inclusionIso.app_hom₃ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).hom).hom₃ = 𝟙 T.obj.obj₃ := sorry

/-- The inverse comparison is the identity at the first vertex. -/
@[simp]
theorem lift.inclusionIso.app_inv₁ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).inv).hom₁ = 𝟙 T.obj.obj₁ := sorry

/-- The inverse comparison is the identity at the second vertex. -/
@[simp]
theorem lift.inclusionIso.app_inv₂ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).inv).hom₂ = 𝟙 T.obj.obj₂ := sorry

/-- The inverse comparison is the identity at the third vertex. -/
@[simp]
theorem lift.inclusionIso.app_inv₃ [P.IsStableUnderShift ℤ]
    (T : P.triangle.FullSubcategory) :
    ((lift.inclusionIso.app P T).inv).hom₃ = 𝟙 T.obj.obj₃ := sorry

/-- Naturality of the comparison between lifted and ambient triangles. -/
theorem lift.inclusionIso.naturality [P.IsStableUnderShift ℤ]
    {T₁ T₂ : P.triangle.FullSubcategory} (f : T₁ ⟶ T₂) :
    (lift P ⋙ P.ι.mapTriangle).map f ≫ (lift.inclusionIso.app P T₂).hom =
      (lift.inclusionIso.app P T₁).hom ≫ P.triangle.ι.map f := sorry

/-- Stacks 0144: lifting a triangle to `P.FullSubcategory` and mapping it back along the
inclusion recovers its original ambient triangle, naturally in the triangle. -/
@[stacks 0144 "comparison between lifted and ambient triangles"]
noncomputable def lift.inclusionIso [P.IsStableUnderShift ℤ] :
    lift P ⋙ P.ι.mapTriangle ≅ P.triangle.ι :=
  NatIso.ofComponents (lift.inclusionIso.app P)
    (fun f ↦ lift.inclusionIso.naturality P f)

end ObjectProperty.triangle

end CategoryTheory
