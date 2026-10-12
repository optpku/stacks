/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangle Maps from Morphisms of Telescope Presentations

The telescope-triangle morphism induced by a compatible presentation map, together with
componentwise, identity, and composition equations.
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

/-- A compatible map of telescope presentations induces a morphism of their telescope
triangles. -/
@[stacks 0CRI "morphism of telescope presentation triangles"]
def triangleMorphism {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y}
    (φ : Hom α P Q) : TriangleMorphism P.triangle Q.triangle where
  hom₁ := ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app
  hom₂ := ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app
  hom₃ := φ.hom
  comm₁ := CoproductCocone.telescopeMap_naturality P.coproduct Q.coproduct α
  comm₂ := φ.toCocone_naturality
  comm₃ := φ.connecting_naturality

/-- The first component of the induced triangle morphism is the explicit coproduct-cocone
map. -/
@[simp]
theorem triangleMorphism.hom₁ {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    (triangleMorphism φ).hom₁ = ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app := sorry

/-- The second component of the induced triangle morphism is the same explicit
coproduct-cocone map. -/
@[simp]
theorem triangleMorphism.hom₂ {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    (triangleMorphism φ).hom₂ = ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app := sorry

/-- The third component of the induced triangle morphism is the map of presented objects. -/
@[simp]
theorem triangleMorphism.hom₃ {S T : ℕ ⥤ D} {α : S ⟶ T}
    {X Y : D} {P : Presentation S X} {Q : Presentation T Y} (φ : Hom α P Q) :
    (triangleMorphism φ).hom₃ = φ.hom := sorry

/-- The triangle morphism induced by the identity presentation morphism is the identity. -/
@[simp]
theorem triangleMorphism_id {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).triangleMorphism = 𝟙 P.triangle := sorry

/-- The triangle morphism induced by a composite of presentation morphisms is the composite
of their triangle morphisms. -/
@[simp]
theorem triangleMorphism_comp
    {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).triangleMorphism =
      TriangleMorphism.comp φ.triangleMorphism ψ.triangleMorphism := sorry

end Presentation.Hom

end CategoryTheory.HomotopyColimit
