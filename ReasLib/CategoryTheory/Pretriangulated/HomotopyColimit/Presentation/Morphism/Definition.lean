module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of Morphisms of Telescope Presentations

The data owner for a map of explicit telescope presentations over a morphism of sequential
diagrams, together with equality and transport along equality of diagram morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism between explicit telescope presentations over a morphism of sequential
diagrams.  It records the map of presented objects and the two squares needed for the
associated morphism of telescope triangles. -/
@[stacks 0CRI "morphism of homotopy-colimit presentations"]
structure Presentation.Hom {S T : ℕ ⥤ D} (α : S ⟶ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) where
  /-- The map between the presented homotopy-colimit objects. -/
  hom : X ⟶ Y
  /-- Compatibility with the maps from the explicitly retained coproduct cocones. -/
  toCoconeComm :
    CommSq P.toCocone (ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app) hom Q.toCocone
  /-- Compatibility with the connecting morphisms after shifting the explicit coproduct map. -/
  connectingComm :
    CommSq P.connecting hom
      ((ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)⟦(1 : ℤ)⟧') Q.connecting

namespace Presentation.Hom

/-- Two morphisms of telescope presentations are equal when their maps between the
presented objects are equal. -/
@[ext]
theorem ext {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} {φ ψ : Hom α P Q}
    (h : φ.hom = ψ.hom) : φ = ψ := sorry

/-- Reindex a morphism of telescope presentations along an equality of the underlying
diagram morphisms. -/
def rebase {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (φ : Hom α P Q) : Hom β P Q :=
  h ▸ φ

/-- Rebasing does not change the map between the presented objects. -/
@[simp]
theorem rebase_hom {S T : ℕ ⥤ D} {α β : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (h : α = β) (φ : Hom α P Q) :
    (rebase h φ).hom = φ.hom := sorry

/-- Rebasing along reflexivity is the identity operation. -/
@[simp]
theorem rebase_rfl {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    rebase rfl φ = φ := sorry

end Presentation.Hom

end CategoryTheory.HomotopyColimit
