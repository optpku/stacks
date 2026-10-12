/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.K0.Action
public import ReasLib.AlgebraicGeometry.Scheme.K0.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.ProjectionFormula

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0'

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f]

/-- Proper pushforward on coherent `K₀'` commutes with the action of perfect-complex `K₀`,
where the perfect class is pulled back along the morphism before acting. -/
theorem projectionFormula (α : K0' X) (β : K0 Y) :
    pushforward f (Action.act X (K0.pullback f β) α) =
      Action.act Y β (pushforward f α) := sorry

end AlgebraicGeometry.Scheme.K0'
