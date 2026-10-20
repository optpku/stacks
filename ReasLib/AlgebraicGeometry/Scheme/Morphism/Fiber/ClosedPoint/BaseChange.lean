module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ClosedPoint
import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField

/-!
# Closed points of scheme-theoretic fibres under base change

This leaf records preservation of fibrewise closed points under arbitrary
base change of a locally finite type morphism.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A point that is closed in its fibre remains closed in the corresponding
fibre after arbitrary base change of a locally finite type morphism. -/
theorem asFiber_mem_closedPoints_of_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme))
    (hx :
      f.asFiber (pullback.fst f g x') ∈
        closedPoints (f.fiber (f (pullback.fst f g x')))) :
    (pullback.snd f g).asFiber x' ∈
      closedPoints ((pullback.snd f g).fiber ((pullback.snd f g) x')) := sorry

end AlgebraicGeometry
