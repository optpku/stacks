/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations

/-!
# Base change for flat pullback of cycles

This file records the compatibility of flat pullback with proper pushforward
in cartesian squares of schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Flat pullback commutes with proper pushforward in a cartesian square of schemes. -/
theorem flatPullback_map_of_isPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X Y X' Y' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (square : IsPullback g'.left f'.left f.left g.left) (r : ℕ)
    [IsProper f.left] [Flat g.left] [Scheme.Hom.RelativeDimension g.left r]
    (k : ℤ) (α : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k) :
    -- Local instance justification (proof-local temporary data): Properness depends on the explicit displayed square and is needed only to type this pushforward.
    letI : IsProper f'.left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance
    -- Local instance justification (proof-local temporary data): Flatness depends on the explicit displayed square and is needed only to type this pullback.
    letI : Flat g'.left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback square.flip inferInstance
    -- Local instance justification (proof-local temporary data): Relative dimension depends on the explicit displayed square and is needed only to type the graded pullback.
    letI : Scheme.Hom.RelativeDimension g'.left r :=
      (Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
        square.flip inferInstance
    flatPullback delta Y' Y g r k
        (mapHom f.left (X.hom.relativeDimensionFunction delta)
          (Y.hom.relativeDimensionFunction delta) k α) =
      mapHom f'.left (X'.hom.relativeDimensionFunction delta)
        (Y'.hom.relativeDimensionFunction delta) (k + (r : ℤ))
        (flatPullback delta X' X g' r k α) := sorry

end AlgebraicGeometry.CycleGroup
