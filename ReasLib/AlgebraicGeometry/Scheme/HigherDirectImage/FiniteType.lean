module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Finite-type higher direct images

This module records finite-type preservation for the top-degree higher direct
image along a proper morphism with bounded relative dimension.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X Y : Scheme.{u}}

/-- If `f : X ⟶ Y` is proper with relative dimension at most `d`, then the
degree-`d` higher direct image of a finite-type quasicoherent `𝒪_X`-module is a
finite-type `𝒪_Y`-module. -/
@[instance]
theorem isFiniteType_of_proper_of_relativeDimensionLE
    (f : X ⟶ Y) [IsProper f] (d : ℕ) [Scheme.Hom.RelativeDimensionLE f d]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    (RingedSpace.Hom.higherDirectImageModule f.toShHom ℱ d).IsFiniteType := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
