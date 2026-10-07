module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.RingTheory.Smooth.EssSmooth

/-!
# Stalk maps of smooth morphisms

A smooth morphism of schemes induces an essentially smooth map on local rings.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Smooth

/-- The map on stalks induced by a smooth morphism of schemes is essentially smooth. -/
theorem essSmooth_stalkMap {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] (x : X) :
    (f.stalkMap x).hom.EssSmooth := sorry

end AlgebraicGeometry.Smooth
