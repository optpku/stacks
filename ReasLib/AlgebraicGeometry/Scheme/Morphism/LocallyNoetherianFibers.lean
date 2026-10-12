/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Fppf

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The property of a scheme morphism whose fibres are locally Noetherian. -/
def LocallyNoetherianFibers : MorphismProperty Scheme.{u} :=
  fun _ Y f ↦ ∀ y : Y, IsLocallyNoetherian (f.fiber y)

namespace LocallyNoetherianFibers

/-- A scheme morphism has locally Noetherian fibres exactly when each of its
scheme-theoretic fibres is locally Noetherian. -/
theorem iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyNoetherianFibers f ↔ ∀ y : Y, IsLocallyNoetherian (f.fiber y) := sorry

/-- Having locally Noetherian fibres is local at the source for the fppf precoverage. -/
instance isLocalAtSourceFppf :
    LocallyNoetherianFibers.IsLocalAtSource Scheme.fppfPrecoverage := sorry

/-- Having locally Noetherian fibres is local at the target for the fppf precoverage. -/
instance isLocalAtTargetFppf :
    LocallyNoetherianFibers.IsLocalAtTarget Scheme.fppfPrecoverage := sorry

end LocallyNoetherianFibers

end AlgebraicGeometry
