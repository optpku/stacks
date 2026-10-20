module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth

/-!
# Smooth morphisms of algebraic spaces are syntomic
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Smooth

/-- A smooth morphism of algebraic spaces is syntomic. -/
instance syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : Syntomic f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Smooth
