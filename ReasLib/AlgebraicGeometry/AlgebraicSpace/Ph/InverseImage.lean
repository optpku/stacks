module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Adjunction
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf

/-!
# Abelian inverse images for the ph and étale topologies

The identity-site inverse image from the big étale slice to the big ph slice,
composed with small-to-big étale inverse image, defines the ph inverse image
of abelian sheaves on the small étale site.
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
    (etaleTopology : GrothendieckTopology (AlgebraicSpace S)) ≤ phTopology S :=
  le_sup_left

/-- Abelian-group-valued sheafification exists on every big ph slice at the
topology-comparison coefficient universe. -/
instance phOver_hasSheafify_addCommGrp (X : AlgebraicSpace S) :
    HasSheafify (bigPhSite X) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Abelian sheaves on big ph slices have injective resolutions at the
topology-comparison coefficient universe. -/
instance phOver_hasInjectiveResolutions (X : AlgebraicSpace S) :
    HasInjectiveResolutions
      (Sheaf (bigPhSite X) AddCommGrpCat.{u + 1}) := by
  infer_instance

/-- Inverse image `ε_X⁻¹` on abelian sheaves from the big étale slice to the big ph slice. -/
abbrev epsilonPullback (X : AlgebraicSpace S) :
    Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} :=
  comparisonTopologyPullbackAb etale_le_ph X

/-- `epsilonPullback` is topology-comparison inverse image along `etale_le_ph`. -/
theorem epsilonPullback_eq (X : AlgebraicSpace S) :
    epsilonPullback X = comparisonTopologyPullbackAb etale_le_ph X := rfl

/-- Inverse image `a_X⁻¹ = π_X⁻¹ ⋙ ε_X⁻¹` on abelian sheaves from the small étale site of `X`
to the big ph slice. -/
abbrev aInverseImage (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (bigPhSite X) AddCommGrpCat.{u + 1} :=
  etalePiInverseImage X ⋙ epsilonPullback X

/-- Inverse image `a_X⁻¹` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
theorem aInverseImage_eq (X : AlgebraicSpace S) :
    aInverseImage X = etalePiInverseImage X ⋙ epsilonPullback X := rfl

/-- Inverse image from the small étale site to the big ph slice carries a constant
abelian sheaf to an isomorphic constant abelian sheaf. -/
theorem aInverseImage_obj_constantSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : AddCommGrpCat.{u + 1}) :
    IsIsomorphic
      ((aInverseImage X).obj
        ((constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A))
      ((constantSheaf (bigPhSite X) AddCommGrpCat.{u + 1}).obj A) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
