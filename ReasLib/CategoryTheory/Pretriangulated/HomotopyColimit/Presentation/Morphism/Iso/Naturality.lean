/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of Invertible Presentation Maps

Compatibility equations for an invertible map of telescope presentations, including the
induced morphism of sequential cocones.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

noncomputable section

namespace CategoryTheory.HomotopyColimit

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Presentation.HomWithIso

/-- Compatibility of an invertible presentation map with the coproduct-to-cocone maps. -/
@[reassoc, stacks 0CRI]
theorem toCocone_naturality {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    P.toCocone ≫ Φ.iso.hom =
      ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app ≫ Q.toCocone := sorry

/-- The inverse object isomorphism transports the target coproduct cocone map back to the
source presentation. -/
@[reassoc, stacks 0CRI]
theorem toCocone_naturality_inv {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app ≫ Q.toCocone ≫ Φ.iso.inv =
      P.toCocone := sorry

/-- Compatibility of an invertible presentation map with the connecting maps. -/
@[reassoc, stacks 0CRI]
theorem connecting_naturality {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    P.connecting ≫ (ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)⟦(1 : ℤ)⟧' =
      Φ.iso.hom ≫ Q.connecting := sorry

/-- The inverse object isomorphism transports the source connecting map to the target after
the shifted coproduct map. -/
@[reassoc, stacks 0CRI]
theorem connecting_naturality_inv {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.iso.inv ≫ P.connecting ≫
        (ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app)⟦(1 : ℤ)⟧' =
      Q.connecting := sorry

/-- An invertible presentation map is compatible with every canonical stage map. -/
@[reassoc, stacks 0CRI]
theorem ι_naturality {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : HomWithIso α P Q) (n : ℕ) :
    P.ι n ≫ Φ.iso.hom = α.app n ≫ Q.ι n := sorry

/-- The inverse object isomorphism transports the target stage map back to the source. -/
@[reassoc, stacks 0CRI]
theorem ι_naturality_inv {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : HomWithIso α P Q) (n : ℕ) :
    α.app n ≫ Q.ι n ≫ Φ.iso.inv = P.ι n := sorry

/-- The cocone morphism underlying an invertible presentation map. -/
@[stacks 0CRI "cocone map of an invertible presentation map"]
def coconeHom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    P.cocone ⟶ (Cocone.precompose α).obj Q.cocone :=
  Φ.toHom.coconeHom

/-- The point map of the induced cocone morphism is the forward object isomorphism. -/
@[simp]
theorem coconeHom_hom {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.coconeHom.hom = Φ.iso.hom := sorry

/-- The point map of the cocone morphism induced by the identity invertible presentation map
is the identity. -/
@[simp]
theorem coconeHom_id_hom {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).coconeHom.hom = 𝟙 X := sorry

/-- The point map of the cocone morphism induced by a composite is the composite of the point
maps. -/
@[simp]
theorem coconeHom_comp_hom
    {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) :
    (comp Φ Ψ).coconeHom.hom = Φ.coconeHom.hom ≫ Ψ.coconeHom.hom := sorry

end Presentation.HomWithIso

end CategoryTheory.HomotopyColimit
