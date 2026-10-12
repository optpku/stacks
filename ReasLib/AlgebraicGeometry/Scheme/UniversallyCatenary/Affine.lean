/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality

/-!
# Universal catenarity of affine schemes

This module transfers universal catenarity from a ring to its prime spectrum.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The spectrum of a universally catenary ring is universally catenary. -/
instance instUniversallyCatenarySpec {R : Type u} [CommRing R]
    [UniversallyCatenaryRing.{u, u} R] :
    UniversallyCatenary (Spec (CommRingCat.of R)) := sorry

end AlgebraicGeometry
