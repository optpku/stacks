/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AffineStructureSheaf
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_18_6

/-!
# Affine étale ringed site of an algebraic space

The structure sheaf `𝒪_X` on the affine étale site of an algebraic space `X` is the restriction
of the small étale structure sheaf along `affineEtaleInclusion`. This packages the ringed site
`(X_affine,étale, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The affine étale site of `X`, equipped with its structure sheaf. -/
abbrev affineRingedSite {S : Scheme.{u}} (X : AlgebraicSpace S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (affineEtaleTopology X) (affineStructureSheaf X)

/-- The structure sheaf of `affineRingedSite X` is the restricted structure sheaf. -/
theorem affineRingedSite_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineRingedSite X).structureSheaf = affineStructureSheaf X :=
  rfl

/-- The site topology of `affineRingedSite X` is `affineEtaleTopology X`. -/
theorem affineRingedSite_siteTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineRingedSite X).siteTopology = affineEtaleTopology X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
