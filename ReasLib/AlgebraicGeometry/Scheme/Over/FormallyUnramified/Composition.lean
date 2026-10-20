module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Composition of formally unramified functor transformations

Formally unramified transformations of functors on schemes over a base are
stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over.FormallyUnramified

/-- The composite of two formally unramified transformations of functors on
schemes over a base is formally unramified. -/
theorem comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallyUnramified a] [FormallyUnramified b] :
    FormallyUnramified (a ≫ b) := sorry

/-- Formally unramified transformations of functors on schemes over a base are
stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyUnramified S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

end AlgebraicGeometry.Scheme.Over.FormallyUnramified
