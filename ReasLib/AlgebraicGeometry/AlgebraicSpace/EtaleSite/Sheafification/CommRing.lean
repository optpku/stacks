module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CommRingSheafification

/-! # Commutative-ring sheafification on the small étale site -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Commutative-ring-valued weak sheafification exists in the original coefficient universe. -/
instance smallEtaleTopology_hasWeakSheafify_commRingCat :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  (CommRingSheafification.ofSpace X).isRightAdjoint

/-- Commutative-ring sheafification equivalences on the small étale site are locally bijective. -/
instance smallEtaleTopology_wEqualsLocallyBijective_commRingCat :
    (smallEtaleTopology X).WEqualsLocallyBijective CommRingCat.{u} := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
