module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
public import ReasLib.RingTheory.Flat.Fiber.CohenMacaulay

/-!
# Cohen--Macaulay morphisms from Cohen--Macaulay schemes

This file records Cohen--Macaulay consequences of flat morphisms whose source
is Cohen--Macaulay.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace CohenMacaulay

/-- A flat morphism from a Cohen--Macaulay scheme to a locally Noetherian
scheme is Cohen--Macaulay. -/
@[stacks 0C0X]
instance of_flat_of_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.CohenMacaulay X] [IsLocallyNoetherian Y] [Flat f] :
    CohenMacaulay f := sorry

end CohenMacaulay

namespace Scheme.CohenMacaulay

/-- For a flat morphism from a Cohen--Macaulay scheme to a locally Noetherian
scheme, every target stalk at a point in the image is Cohen--Macaulay. -/
@[stacks 0C0X]
instance instTargetStalkOfFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Scheme.CohenMacaulay X] [IsLocallyNoetherian Y] [Flat f] (x : X) :
    CohenMacaulayRing (Y.presheaf.stalk (f x)) := sorry

end Scheme.CohenMacaulay
end AlgebraicGeometry
