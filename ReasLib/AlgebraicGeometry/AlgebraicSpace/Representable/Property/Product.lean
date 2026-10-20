module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Products of transferred morphism properties of algebraic spaces

The transfer of a morphism property of algebraic spaces to presheaf morphisms
is closed under binary products of maps when the property is stable under
base change, fppf local on the target, and stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If two morphisms of presheaves are representable by algebraic spaces and
have a property stable under base change, fppf local on the target, and stable
under composition, then their binary product is representable by algebraic
spaces and has the same property. -/
theorem relativeAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (fppfPrecoverage S)] [P.IsStableUnderComposition]
    {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (ha₁ : relativeAlgebraicSpaces P a₁) (ha₂ : relativeAlgebraicSpaces P a₂) :
    relativeAlgebraicSpaces P (prod.map a₁ a₂) := sorry

end AlgebraicGeometry.AlgebraicSpace
