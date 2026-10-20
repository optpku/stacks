module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.LocalCompleteIntersection

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every syntomic morphism of schemes is a Gorenstein morphism. -/
instance instGorensteinOfSyntomic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Syntomic f] : Gorenstein f := sorry

end AlgebraicGeometry
