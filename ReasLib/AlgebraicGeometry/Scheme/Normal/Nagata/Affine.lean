module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality

@[expose] public section

/-!
# Nagata affine schemes

The spectrum of a Nagata ring is a Nagata scheme.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The spectrum of a Nagata ring is a Nagata scheme. -/
instance instNagataSpec (R : CommRingCat) [NagataRing R] : Nagata (Spec R) := sorry

end AlgebraicGeometry.Scheme
