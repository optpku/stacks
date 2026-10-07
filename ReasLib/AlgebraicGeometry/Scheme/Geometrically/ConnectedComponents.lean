module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Connected components of geometrically connected pullbacks

This module gives bijectivity of the maps on connected components induced by the projections of
a pullback along a geometrically connected morphism over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace GeometricallyConnected

/-- The second projection of a pullback along a geometrically connected morphism over a field
induces a bijection on connected components. -/
theorem pullbackSndConnectedComponentsMap_bijective
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyConnected f] :
    Function.Bijective
      (((pullback.snd f g).continuous.connectedComponentsMap) :
        ConnectedComponents (pullback f g : Scheme.{u}) → ConnectedComponents Y) := sorry

/-- The first projection of a pullback along a geometrically connected morphism over a field
induces a bijection on connected components. -/
theorem pullbackFstConnectedComponentsMap_bijective
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyConnected g] :
    Function.Bijective
      (((pullback.fst f g).continuous.connectedComponentsMap) :
        ConnectedComponents (pullback f g : Scheme.{u}) → ConnectedComponents X) := sorry

end GeometricallyConnected

end AlgebraicGeometry
