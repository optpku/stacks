module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Universally closed morphisms of algebraic spaces are quasi-compact

A universally closed morphism of algebraic spaces over a scheme is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-- A universally closed morphism of algebraic spaces over a scheme is quasi-compact. -/
instance of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] : QuasiCompact f := sorry

end AlgebraicGeometry.AlgebraicSpace.QuasiCompact
