/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangle Maps from Invertible Presentation Maps

The morphism of telescope triangles associated to an invertible map of explicit
presentations, together with its componentwise computation API.
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

/-- The telescope-triangle morphism underlying an invertible presentation map. -/
@[stacks 0CRI "triangle map of an invertible presentation map"]
def triangleMorphism {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y}
    (Φ : HomWithIso α P Q) : TriangleMorphism P.triangle Q.triangle :=
  Φ.toHom.triangleMorphism

/-- The first triangle component is the explicit coproduct map induced by the diagram map. -/
@[simp]
theorem triangleMorphism.hom₁ {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.triangleMorphism.hom₁ =
      ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app := sorry

/-- The second triangle component is the explicit coproduct map induced by the diagram map. -/
@[simp]
theorem triangleMorphism.hom₂ {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.triangleMorphism.hom₂ =
      ColimitCocone.Discrete.map P.coproduct Q.coproduct α.app := sorry

/-- The third triangle component is the forward object isomorphism. -/
@[simp]
theorem triangleMorphism.hom₃ {S T : ℕ ⥤ D} {α : S ⟶ T} {X Y : D}
    {P : Presentation S X} {Q : Presentation T Y} (Φ : HomWithIso α P Q) :
    Φ.triangleMorphism.hom₃ = Φ.iso.hom := sorry

/-- The triangle morphism induced by the identity invertible presentation map is the
identity. -/
@[simp]
theorem triangleMorphism_id {S : ℕ ⥤ D} {X : D} (P : Presentation S X) :
    (id P).triangleMorphism = 𝟙 P.triangle := sorry

/-- The triangle morphism induced by a composite is the composite of the induced triangle
morphisms. -/
@[simp]
theorem triangleMorphism_comp
    {S₀ S₁ S₂ : ℕ ⥤ D} {α : S₀ ⟶ S₁} {β : S₁ ⟶ S₂}
    {X₀ X₁ X₂ : D} {P : Presentation S₀ X₀} {Q : Presentation S₁ X₁}
    {R : Presentation S₂ X₂} (Φ : HomWithIso α P Q) (Ψ : HomWithIso β Q R) :
    (comp Φ Ψ).triangleMorphism =
      TriangleMorphism.comp Φ.triangleMorphism Ψ.triangleMorphism := sorry

end Presentation.HomWithIso

end CategoryTheory.HomotopyColimit
