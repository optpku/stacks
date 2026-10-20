module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat

/-!
# Flatness of syntomic morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Syntomic

/-- A syntomic morphism of algebraic spaces is flat. -/
instance flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Syntomic f] : Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Syntomic
