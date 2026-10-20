module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Syntomic morphisms of algebraic spaces are universally open
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A syntomic morphism of algebraic spaces is universally open. -/
instance UniversallyOpen.of_syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Syntomic f] : UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
