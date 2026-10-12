/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Composition of formally smooth functor transformations

Formally smooth transformations of functors on schemes over a base are stable
under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Over.FormallySmooth

/-- The composite of two formally smooth transformations of functors on
schemes over a base is formally smooth. -/
theorem comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (b : G ⟶ H) [FormallySmooth a] [FormallySmooth b] :
    FormallySmooth (a ≫ b) := sorry

/-- Formally smooth transformations of functors on schemes over a base are
stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallySmooth S : MorphismProperty ((Over S)ᵒᵖ ⥤ Type v)) := sorry

end AlgebraicGeometry.Scheme.Over.FormallySmooth
