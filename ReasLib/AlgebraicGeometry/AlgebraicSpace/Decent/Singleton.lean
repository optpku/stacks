module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Decent algebraic spaces with a singleton underlying space

A decent algebraic space whose space of points is a singleton is a scheme. If it
is moreover reduced, it is isomorphic over the base to the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsScheme

/-- A decent algebraic space with exactly one point is a scheme. -/
instance of_singleton_points {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [Nonempty (Points X)] [Subsingleton (Points X)] :
    IsScheme X := sorry

end IsScheme

/-- A reduced decent algebraic space with exactly one point is isomorphic over
its base scheme to the spectrum of a field. -/
theorem exists_iso_spec_of_singleton {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [IsReduced X] [Nonempty (Points X)] [Subsingleton (Points X)] :
    ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
      Nonempty (X ≅ ofOver (Over.mk σ)) := sorry

end AlgebraicGeometry.AlgebraicSpace
