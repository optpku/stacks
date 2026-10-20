module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Composition of formally étale functor transformations

Formally étale transformations of functors on schemes over a base are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over.FormallyEtale

/-- The composite of two formally étale transformations of functors on
schemes over a base is formally étale. -/
theorem comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallyEtale a] [FormallyEtale b] :
    FormallyEtale (a ≫ b) := sorry

/-- Formally étale transformations of functors on schemes over a base are
stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyEtale S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

end AlgebraicGeometry.Scheme.Over.FormallyEtale
