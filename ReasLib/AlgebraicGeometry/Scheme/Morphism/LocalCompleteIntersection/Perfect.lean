/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul
public import ReasLib.RingTheory.RingHom.Perfect.Basic

/-!
# Local complete intersection morphisms and perfect factors

This module records consequences for a commutative triangle whose first morphism is perfect and
whose composite is a local complete intersection morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfType

/-- In a commutative triangle of scheme morphisms over a locally Noetherian base, a perfect first
morphism is a local complete intersection when the second morphism is locally of finite type and
the composite is a local complete intersection. -/
@[stacks 09RL]
theorem isLocalCompleteIntersection_of_perfect_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    (hf : LocallyOfType RingHom.IsPerfectRingMap f)
    (hX : LocallyOfType RingHom.IsLocalCompleteIntersection h) :
    LocallyOfType RingHom.IsLocalCompleteIntersection f := sorry

end AlgebraicGeometry.LocallyOfType

namespace AlgebraicGeometry.Scheme.Hom

/-- In a commutative triangle of scheme morphisms over a locally Noetherian base, if the first
morphism is perfect, the second is locally of finite type, and the composite is a local complete
intersection, then the second morphism is Koszul at every point in the image of the first. -/
@[stacks 09RL]
theorem koszulAt_image_of_perfect_of_comp
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (hcomm : f ≫ g = h) [IsLocallyNoetherian S] [LocallyOfFiniteType g]
    (hf : LocallyOfType RingHom.IsPerfectRingMap f)
    (hX : LocallyOfType RingHom.IsLocalCompleteIntersection h) :
    ∀ x : X, g.KoszulAt (f x) := sorry

end AlgebraicGeometry.Scheme.Hom
