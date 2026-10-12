/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of Morphisms of Telescope Presentations

Compatibility equations at the coproduct, connecting-map, stage, and sequential-cocone
levels for a map of explicit telescope presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.Hom

/-- The square with the coproduct-to-cocone maps stored by a presentation morphism. -/
@[reassoc, stacks 0CRI]
theorem toCocone_naturality {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    P.toCocone ≫ φ.hom =
      ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app ≫ Q.toCocone := sorry

/-- The square with the connecting maps stored by a presentation morphism. -/
@[reassoc, stacks 0CRI]
theorem connecting_naturality {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    P.connecting ≫ (ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)⟦(1 : ℤ)⟧' =
      φ.hom ≫ Q.connecting := sorry

/-- A morphism of telescope presentations is compatible with every canonical stage map. -/
@[reassoc, stacks 0CRI]
theorem ι_naturality {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Hom α P Q) (n : ℕ) :
    P.ι n ≫ φ.hom = α.app n ≫ Q.ι n := sorry

/-- The cocone-morphism compatibility equation induced by a morphism of telescope
presentations. -/
theorem coconeHom_w {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Hom α P Q) (n : ℕ) :
    P.cocone.ι.app n ≫ φ.hom =
      ((Cocone.precompose α).obj Q.cocone).ι.app n := sorry

/-- A morphism of telescope presentations induces a morphism from the source cocone to the
target cocone precomposed along the diagram map. -/
@[stacks 0CRI]
def coconeHom {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Hom α P Q) : P.cocone ⟶ (Cocone.precompose α).obj Q.cocone where
  hom := φ.hom
  w := coconeHom_w φ

/-- The map on cocone points induced by a presentation morphism is its underlying map. -/
@[simp]
theorem coconeHom_hom {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Hom α P Q) : φ.coconeHom.hom = φ.hom := sorry

/-- The point map of the cocone morphism induced by the identity presentation morphism is
the identity. -/
@[simp]
theorem coconeHom_id_hom {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).coconeHom.hom = 𝟙 X := sorry

/-- The point map of the cocone morphism induced by a composite is the composite of the point
maps. -/
@[simp]
theorem coconeHom_comp_hom
    {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).coconeHom.hom = φ.coconeHom.hom ≫ ψ.coconeHom.hom := sorry

end Presentation.Hom

end CategoryTheory.HomotopyColimit
