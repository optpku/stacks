/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of Morphisms of Homotopy-Limit Presentations

Compatibility equations at the product, connecting-map, stage, and sequential-cone levels
for a map of explicit Milnor presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyLimit

open SequentialInverseSystem.Milnor

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Hom

/-- The square with the product inclusions stored by a presentation morphism. -/
@[reassoc, stacks 08TC]
theorem ι_naturality {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) :
    P.ι ≫ ProductCone.map P.product Q.product α = φ.hom ≫ Q.ι := sorry

/-- The square with the connecting maps stored by a presentation morphism. -/
@[reassoc, stacks 08TC]
theorem connecting_naturality {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) :
    P.connecting ≫ φ.hom⟦(1 : ℤ)⟧' =
      ProductCone.map P.product Q.product α ≫ Q.connecting := sorry

/-- A morphism of homotopy-limit presentations is compatible with every canonical stage
projection. -/
@[reassoc, stacks 08TC]
theorem stageProjection_naturality {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) (n : ℕ) :
    P.stageProjection n ≫ α.app (op n) =
      φ.hom ≫ Q.stageProjection n := sorry

/-- The cone-morphism compatibility equation induced by a morphism of homotopy-limit
presentations. -/
theorem coneHom_w {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) (j : ℕᵒᵖ) :
    φ.hom ≫ Q.cone.π.app j =
      ((Cone.postcompose α).obj P.cone).π.app j := sorry

/-- A morphism of homotopy-limit presentations induces a morphism from the source cone
postcomposed along the tower map to the target presentation cone. -/
@[stacks 08TC]
def coneHom {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) : (Cone.postcompose α).obj P.cone ⟶ Q.cone where
  hom := φ.hom
  w := coneHom_w φ

/-- The map on cone points induced by a presentation morphism is its underlying map. -/
@[simp]
theorem coneHom_hom {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) : φ.coneHom.hom = φ.hom := sorry

/-- The point map of the cone morphism induced by the identity presentation morphism is the
identity. -/
@[simp]
theorem coneHom_id_hom {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    (id P).coneHom.hom = 𝟙 X := sorry

/-- The point map of the cone morphism induced by a composite is the composite of the point
maps. -/
@[simp]
theorem coneHom_comp_hom
    {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).coneHom.hom = φ.coneHom.hom ≫ ψ.coneHom.hom := sorry

end Presentation.Hom

end CategoryTheory.HomotopyLimit
