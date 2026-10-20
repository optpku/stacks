module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point

/-!
# Reducedness of proper flat algebraic spaces over discrete valuation rings

A proper flat algebraic space over a discrete valuation ring with reduced special
fibre is reduced, and its generic fibre is reduced as well.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper flat algebraic space over the spectrum of a discrete valuation ring is
reduced if its special fibre is reduced. -/
@[stacks 0E0B]
theorem isReduced_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))] :
    IsReduced X :=
  sorry

/-- The generic fibre of a proper flat algebraic space over the spectrum of a discrete
valuation ring is reduced if its special fibre is reduced. -/
@[stacks 0E0B]
theorem isReduced_genericFiber_of_proper_flat_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
    [Proper f] [Flat f]
    [IsReduced (fiber f (IsLocalRing.closedPoint R))] :
    IsReduced (fiber f (genericPoint (Spec (CommRingCat.of R)))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
