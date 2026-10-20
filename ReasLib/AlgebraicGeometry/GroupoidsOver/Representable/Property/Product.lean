module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.CategoryTheory.Fibered.Groupoids.Product

/-!
# Products of representable morphisms having a morphism property

Properties of algebraic-space morphisms stable under base change and composition
and fppf local on the target are inherited by binary products of representable
1-morphisms of groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- If a property of algebraic-space morphisms is stable under base change and
composition and fppf local on the target, the binary product of two 1-morphisms
of groupoid fibrations representable by algebraic spaces having that property
also has that property. -/
theorem has.prod_map {S : Scheme.{u}} {X₁ X₂ Y₁ Y₂ : GroupoidsOver S}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    [P.IsStableUnderComposition]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hf₁ : relativelyRepresentableByAlgebraicSpaces f₁)
    (hf₂ : relativelyRepresentableByAlgebraicSpaces f₂)
    (hf₁P : has P f₁) (hf₂P : has P f₂) : has P (prodMap f₁ f₂) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
