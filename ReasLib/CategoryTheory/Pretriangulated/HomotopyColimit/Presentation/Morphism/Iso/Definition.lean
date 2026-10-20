module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Definition of Invertible Presentation Maps

This leaf refines a morphism of explicit telescope presentations by requiring its map on
presented objects to be an isomorphism.  The underlying diagram morphism need not be
invertible; this distinction is important for cofinal maps such as passage to a subsequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A morphism of explicit telescope presentations whose map on the presented objects is
invertible.  No invertibility is required of the underlying morphism of sequential diagrams. -/
@[stacks 0CRI "invertible map of homotopy-colimit presentations"]
structure Presentation.HomWithIso {S T : ℕ ⥤ D} (α : S ⟶ T)
    {X Y : D} (P : Presentation S X) (Q : Presentation T Y) where
  /-- The isomorphism between the presented homotopy-colimit objects. -/
  iso : X ≅ Y
  /-- Compatibility with the maps from the explicitly retained coproduct cocones. -/
  toCoconeComm :
    CommSq P.toCocone (ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)
      iso.hom Q.toCocone
  /-- Compatibility with the connecting morphisms after shifting the explicit coproduct map. -/
  connectingComm :
    CommSq P.connecting iso.hom
      ((ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)⟦(1 : ℤ)⟧') Q.connecting

namespace Presentation.HomWithIso

/-- Two invertible presentation maps are equal when their retained object isomorphisms are
equal. -/
@[ext]
theorem ext {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} {Φ Ψ : HomWithIso α P Q}
    (h : Φ.iso = Ψ.iso) : Φ = Ψ := sorry

/-- Forget invertibility of the object map in an invertible presentation morphism. -/
@[stacks 0CRI "forget invertibility of a presentation map"]
def toHom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : HomWithIso α P Q) : Presentation.Hom α P Q where
  hom := Φ.iso.hom
  toCoconeComm := Φ.toCoconeComm
  connectingComm := Φ.connectingComm

/-- Equip a presentation morphism with the canonical isomorphism determined by an
`IsIso` instance on its object map. -/
@[stacks 0CRI "promote an invertible presentation map"]
def ofHom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (φ : Presentation.Hom α P Q) [IsIso φ.hom] : HomWithIso α P Q where
  iso := asIso φ.hom
  toCoconeComm := φ.toCoconeComm
  connectingComm := φ.connectingComm

/-- The underlying map is the forward map of the retained object isomorphism. -/
@[simp]
theorem toHom_hom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.toHom.hom = Φ.iso.hom := sorry

/-- Promoting an invertible presentation morphism and then forgetting invertibility recovers
the original morphism. -/
@[simp]
theorem ofHom_toHom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (φ : Presentation.Hom α P Q) [IsIso φ.hom] :
    (ofHom φ).toHom = φ := sorry

/-- The forward map of the promoted object isomorphism is the original object map. -/
@[simp]
theorem ofHom_iso_hom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (φ : Presentation.Hom α P Q) [IsIso φ.hom] :
    (ofHom φ).iso.hom = φ.hom := sorry

end Presentation.HomWithIso

end CategoryTheory.HomotopyColimit
