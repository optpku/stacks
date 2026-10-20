module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finitely presented higher direct images

This module records finite-presentation preservation for the top-degree higher
direct image along a proper finitely presented morphism with bounded relative
dimension.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X Y : Scheme.{u}}

/-- If `f : X ⟶ Y` is a proper finitely presented morphism with relative
dimension at most `d`, then the degree-`d` higher direct image of a finitely
presented `𝒪_X`-module is a finitely presented `𝒪_Y`-module. -/
@[instance]
theorem isFinitePresentation_topDegree
    (f : X ⟶ Y) [IsProper f] [Scheme.Hom.FinitePresentation f]
    (d : ℕ) [Scheme.Hom.RelativeDimensionLE f d]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ d).IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
