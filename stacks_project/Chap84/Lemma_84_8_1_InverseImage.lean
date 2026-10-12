/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig
public import stacks_project.Chap84.Lemma_84_6_6_InverseImage
public import stacks_project.Chap84.Lemma_84_8_4_Comparison

/-!
# Ph/étale inverse images of algebraic spaces

This leaf owns the comparison `étale ≤ ph` on algebraic spaces, the identity-site inverse
image `ε_X⁻¹`, the composite `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves, and the named
sheafify / injective-resolution instances on big ph slices.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

variable {S : Scheme.{u}}

/-- Every étale covering of algebraic spaces over `S` is a ph covering. -/
theorem etale_le_ph :
    (etaleTopology : GrothendieckTopology (AlgebraicSpace S)) ≤ phTopology S := sorry

/-- Abelian-group-valued sheafification exists on every big ph slice at the
topology-comparison coefficient universe. -/
instance phOver_hasSheafify_addCommGrp (X : AlgebraicSpace S) :
    HasSheafify (bigPhSite X) AddCommGrpCat.{u + 1} := sorry

/-- Abelian sheaves on big ph slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance phOver_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions
      (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) := sorry

/-- Inverse image `ε_X⁻¹` on abelian sheaves from the big étale slice to the big ph slice. -/
abbrev epsilonPullback (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPullbackAb etale_le_ph X

/-- `epsilonPullback` is topology-comparison inverse image along `etale_le_ph`. -/
theorem epsilonPullback_eq (X : AlgebraicSpace S) :
    epsilonPullback X = comparisonTopologyPullbackAb etale_le_ph X := sorry

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves from the small étale site of `X`
to the big ph slice. -/
abbrev aInverseImage (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} :=
  etalePiInverseImage X ⋙ epsilonPullback X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseImage_eq (X : AlgebraicSpace S) :
    aInverseImage X = etalePiInverseImage X ⋙ epsilonPullback X := sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
