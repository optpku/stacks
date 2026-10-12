/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pushout

variable {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y}
  {f' : X' ⟶ Y'} {g : Y ⟶ Y'}

/-- The map on section rings along the lower horizontal morphism in a commutative
square of schemes, with its codomain transported to the iterated inverse-image open. -/
def sectionMap (sq : CommSq i f f' g) (U : Y'.Opens) :
    Γ(Y, g ⁻¹ᵁ U) ⟶ Γ(X, i ⁻¹ᵁ (f' ⁻¹ᵁ U)) :=
  f.appLE (g ⁻¹ᵁ U) (i ⁻¹ᵁ (f' ⁻¹ᵁ U))
    (congrArg (fun h : X ⟶ Y' ↦ h ⁻¹ᵁ U) sq.w).le

/-- The section-ring maps induced by a commutative square of schemes commute. -/
theorem sectionMap_comm (sq : CommSq i f f' g) (U : Y'.Opens) :
    g.app U ≫ sectionMap sq U = f'.app U ≫ i.app (f' ⁻¹ᵁ U) := sorry

/-- A commutative square of schemes realizes the structure sheaf on its lower-right
corner as the sectionwise pullback of the other three structure sheaves. -/
def IsStructureSheafPullback (sq : CommSq i f f' g) : Prop :=
  ∀ U : Y'.Opens,
    IsPullback (g.app U) (f'.app U) (sectionMap sq U) (i.app (f' ⁻¹ᵁ U))

namespace IsStructureSheafPullback

/-- The pullback square of section rings associated to an open set. -/
theorem app (sq : CommSq i f f' g) (h : IsStructureSheafPullback sq) (U : Y'.Opens) :
    IsPullback (g.app U) (f'.app U) (sectionMap sq U) (i.app (f' ⁻¹ᵁ U)) := sorry

end IsStructureSheafPullback

end AlgebraicGeometry.Scheme.Pushout
