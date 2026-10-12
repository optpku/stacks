/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangle Maps from Morphisms of Homotopy-Limit Presentations

The Milnor-triangle morphism induced by a compatible presentation map, together with
componentwise, identity, and composition equations.
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

/-- A compatible map of homotopy-limit presentations induces a morphism of their Milnor
triangles. -/
@[stacks 08TC "morphism of Milnor presentation triangles"]
def triangleMorphism {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) : TriangleMorphism P.triangle Q.triangle where
  hom₁ := φ.hom
  hom₂ := ProductCone.map P.product Q.product α
  hom₃ := ProductCone.map P.product Q.product α
  comm₁ := φ.ι_naturality
  comm₂ := ProductCone.difference_naturality P.product Q.product α
  comm₃ := φ.connecting_naturality

/-- The first component of the induced triangle morphism is the map of presented objects. -/
@[simp]
theorem triangleMorphism.hom₁ {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) :
    (triangleMorphism φ).hom₁ = φ.hom := sorry

/-- The second component of the induced triangle morphism is the explicit product-cone map. -/
@[simp]
theorem triangleMorphism.hom₂ {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) :
    (triangleMorphism φ).hom₂ = ProductCone.map P.product Q.product α := sorry

/-- The third component of the induced triangle morphism is the same explicit product-cone
map. -/
@[simp]
theorem triangleMorphism.hom₃ {K L : SequentialInverseSystem D} {α : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Hom α P Q) :
    (triangleMorphism φ).hom₃ = ProductCone.map P.product Q.product α := sorry

/-- The triangle morphism induced by the identity presentation morphism is the identity. -/
@[simp]
theorem triangleMorphism_id {K : SequentialInverseSystem D} {X : D}
    (P : Presentation K X) :
    (id P).triangleMorphism = 𝟙 P.triangle := sorry

/-- The triangle morphism induced by a composite of presentation morphisms is the composite
of their triangle morphisms. -/
@[simp]
theorem triangleMorphism_comp
    {K₀ K₁ K₂ : SequentialInverseSystem D} {α : K₀ ⟶ K₁} {β : K₁ ⟶ K₂}
    {X₀ X₁ X₂ : D} {P : Presentation K₀ X₀} {Q : Presentation K₁ X₁}
    {R : Presentation K₂ X₂} (φ : Hom α P Q) (ψ : Hom β Q R) :
    (comp φ ψ).triangleMorphism =
      TriangleMorphism.comp φ.triangleMorphism ψ.triangleMorphism := sorry

end Presentation.Hom

end CategoryTheory.HomotopyLimit
