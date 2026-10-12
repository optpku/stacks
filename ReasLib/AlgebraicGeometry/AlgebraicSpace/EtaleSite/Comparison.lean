/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces

/-!
# Comparisons of étale sheaf topoi

The small, spaces, and affine étale sites give equivalent categories of
type-valued sheaves through their canonical site inclusions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The direct image from the small étale site to the spaces-étale site is an equivalence on
sheaves of types. -/
instance smallEtaleInclusion_directImage_isEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (SmallEtale.topology X) (spacesEtaleTopology X)).IsEquivalence := sorry

/-- The direct image from the affine étale site to the small étale site is an equivalence on
sheaves of types. -/
instance affineEtaleInclusion_directImage_isEquivalence {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ((affineEtaleInclusion X).sheafPushforwardCocontinuous (Type (u + 1))
      (affineEtaleTopology X) (SmallEtale.topology X)).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace
