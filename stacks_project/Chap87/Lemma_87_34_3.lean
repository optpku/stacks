/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_18_11
public import stacks_project.Chap87.Lemma_87_34_3_Reduction
import StacksCheckRecall

/-!
# Lemma 87.34.3

If `f : X ⟶ Y` is a morphism of formal algebraic spaces over a scheme `S`
that is representable by algebraic spaces and étale, then `X_red = X ×_Y Y_red`
and the induced map of algebraic-space reductions is étale. Postcomposition
along that map is a cocontinuous functor `j : X_étale ⥤ Y_étale` of small
étale sites, the morphism of topoi `f_small` is the algebraic-space small
étale topos morphism of that map, identified with the Sites, Lemma 7.21.1
construction of `j`, and `j` is continuous, so Sites, Lemma 7.21.5 applies.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Functor
open AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [Reduction X] [Reduction Y]

/-- Lemma 87.34.3 (1): if `f : X ⟶ Y` is a morphism of formal algebraic spaces
over a scheme `S` that is representable by algebraic spaces and étale, then
`AlgebraicSpace.Etale (inducedReductionMap f)`, and postcomposition
`j := AlgebraicSpace.etaleRestriction (inducedReductionMap f)` is a
cocontinuous functor `X_étale ⥤ Y_étale` on `AlgebraicSpace.smallEtaleSite`
of the Lemma 87.12.1 reductions `reduction X` and `reduction Y`. -/
@[stacks 0DED]
abbrev etaleRestriction (f : X ⟶ Y) [Etale f] :
    AlgebraicSpace.smallEtaleSite (reduction X) ⥤
      AlgebraicSpace.smallEtaleSite (reduction Y) :=
  AlgebraicSpace.etaleRestriction (inducedReductionMap f)

/-- `etaleRestriction f` is postcomposition along `inducedReductionMap f`. -/
theorem etaleRestriction_def (f : X ⟶ Y) [Etale f] :
    etaleRestriction f = AlgebraicSpace.etaleRestriction (inducedReductionMap f) :=
  sorry

/-- Postcomposition along `inducedReductionMap f` is cocontinuous. -/
instance etaleRestriction_isCocontinuous (f : X ⟶ Y) [Etale f] :
    (etaleRestriction f).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology (reduction X))
      (AlgebraicSpace.smallEtaleTopology (reduction Y)) :=
  sorry

/-- Lemma 87.34.3 (2): the morphism of topoi `f_small` is
`AlgebraicSpace.smallEtaleMorphismOfTopoi (inducedReductionMap f)`, and its
inverse image is identified with the Sites, Lemma 7.21.1 pullback of
`AlgebraicSpace.etaleRestriction (inducedReductionMap f)` by specializing
`AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous`. -/
@[stacks 0DED]
abbrev smallEtaleMorphismOfTopoi (f : X ⟶ Y) [Etale f] :=
  AlgebraicSpace.smallEtaleMorphismOfTopoi (inducedReductionMap f)

/-- `smallEtaleMorphismOfTopoi f` is the small étale topos morphism of
`inducedReductionMap f`. -/
theorem smallEtaleMorphismOfTopoi_def (f : X ⟶ Y) [Etale f] :
    smallEtaleMorphismOfTopoi f =
      AlgebraicSpace.smallEtaleMorphismOfTopoi (inducedReductionMap f) :=
  sorry

/-- Inverse image along `smallEtaleMorphismOfTopoi f` is identified with
cocontinuous sheaf pullback along `etaleRestriction f` by specializing
`AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous`. -/
noncomputable def smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    (f : X ⟶ Y) [Etale f] :
    (smallEtaleMorphismOfTopoi f).inverseImage ≅
      (etaleRestriction f).sheafPullbackCocontinuous (Type (u + 1))
        (AlgebraicSpace.smallEtaleTopology (reduction X))
        (AlgebraicSpace.smallEtaleTopology (reduction Y)) :=
  AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
    (inducedReductionMap f)

/-- `smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous` is the specialization
of `AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous` to
`inducedReductionMap f`. -/
theorem smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous_spec
    (f : X ⟶ Y) [Etale f] :
    smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous f =
      AlgebraicSpace.smallEtaleMorphismOfTopoi_sheafPullbackCocontinuous
        (inducedReductionMap f) :=
  sorry

/-- Lemma 87.34.3 (3): `etaleRestriction f` is continuous as well, hence
Sites, Lemma 7.21.5 applies. -/
@[stacks 0DED]
instance etaleRestriction_isContinuous (f : X ⟶ Y) [Etale f] :
    (etaleRestriction f).IsContinuous
      (AlgebraicSpace.smallEtaleTopology (reduction X))
      (AlgebraicSpace.smallEtaleTopology (reduction Y)) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace

#check Functor.sheafPushforwardContinuousCompSheafToPresheafIso
#check Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
#check Functor.sheafAdjunctionCocontinuous
