module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Flatness and composite fibres

This leaf records pointwise flatness of the canonical morphism from a composite
fibre to the corresponding base-changed intermediate fibre.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If the first of two scheme morphisms is flat at a point, then the canonical
morphism from the composite fibre to the base-changed intermediate fibre is
flat at the corresponding point. -/
theorem flatAt_compFiberToBaseFiber_of_flatAt {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X) (hflat : flatAt f x) :
    flatAt (compFiberToBaseFiber f g (g (f x))) ((f ≫ g).asFiber x) := sorry

end AlgebraicGeometry.Scheme.Hom
