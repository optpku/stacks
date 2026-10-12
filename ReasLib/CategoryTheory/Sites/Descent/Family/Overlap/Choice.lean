/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Overlap

/-!
# Canonical choices of family overlap presentations

This leaf constructs actual pairwise and threefold overlap presentations from family-local
pullback assumptions.  The middle pullback and outer lift are explicit constructions; no
presentation is extracted from a `Nonempty` witness.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace SemiRepresentableFamily.Over.OverlapPresentation

variable {C : Type u} [Category.{v} C]
variable {U : C} {𝒰 : SemiRepresentableFamily.Over.{w} U}

section FamilyLocal

variable [𝒰.toPresieve.HasPairwisePullbacks] [𝒰.HasTripleOverlaps]

/-- The selected pullback of the two middle projections used in a threefold family overlap. -/
noncomputable def chosenMiddle (i j k : 𝒰.index) :
    ChosenPullback (𝒰.snd i j) (𝒰.fst j k) :=
  ChosenPullback.ofHasPullbackProof (HasTripleOverlaps.triple i j k)

/-- The outer legs of the selected middle pullback define a compatible cone over the outer
pairwise overlap. -/
theorem chosenOuterCondition (i j k : 𝒰.index) :
    ((chosenMiddle (𝒰 := 𝒰) i j k).p₁ ≫ 𝒰.fst i j) ≫ (𝒰.obj i).hom =
      ((chosenMiddle (𝒰 := 𝒰) i j k).p₂ ≫ 𝒰.snd j k) ≫ (𝒰.obj k).hom := sorry

/-- The explicit morphism from the selected middle pullback to the outer pairwise overlap. -/
noncomputable def chosenOuterLiftMap (i j k : 𝒰.index) :
    (chosenMiddle (𝒰 := 𝒰) i j k).pullback ⟶ 𝒰.Overlap i k :=
  (𝒰.chosenOverlap i k).isPullback.lift
    ((chosenMiddle (𝒰 := 𝒰) i j k).p₁ ≫ 𝒰.fst i j)
    ((chosenMiddle (𝒰 := 𝒰) i j k).p₂ ≫ 𝒰.snd j k)
    (chosenOuterCondition (𝒰 := 𝒰) i j k)

namespace chosenOuterLiftMap

/-- The outer lift has the expected first projection. -/
theorem fst (i j k : 𝒰.index) :
    chosenOuterLiftMap (𝒰 := 𝒰) i j k ≫ 𝒰.fst i k =
      (chosenMiddle (𝒰 := 𝒰) i j k).p₁ ≫ 𝒰.fst i j := sorry

/-- The outer lift has the expected second projection. -/
theorem snd (i j k : 𝒰.index) :
    chosenOuterLiftMap (𝒰 := 𝒰) i j k ≫ 𝒰.snd i k =
      (chosenMiddle (𝒰 := 𝒰) i j k).p₂ ≫ 𝒰.snd j k := sorry

/-- The outer lift has the expected common map to the target of the family. -/
theorem overlapMap (i j k : 𝒰.index) :
    chosenOuterLiftMap (𝒰 := 𝒰) i j k ≫ 𝒰.overlapMap i k =
      (chosenMiddle (𝒰 := 𝒰) i j k).p₁ ≫ 𝒰.overlapMap i j := sorry

end chosenOuterLiftMap

/-- The explicit outer-lift package used to assemble the selected threefold overlap. -/
noncomputable def chosenOuterLift (i j k : 𝒰.index) :
    ChosenPullback₃.MiddleLift
      (𝒰.chosenOverlap i j) (𝒰.chosenOverlap j k) (𝒰.chosenOverlap i k)
      (chosenMiddle (𝒰 := 𝒰) i j k) where
  f := chosenOuterLiftMap (𝒰 := 𝒰) i j k
  f_p₁ := chosenOuterLiftMap.fst (𝒰 := 𝒰) i j k
  f_p₂ := chosenOuterLiftMap.snd (𝒰 := 𝒰) i j k
  f_p := chosenOuterLiftMap.overlapMap (𝒰 := 𝒰) i j k

/-- The selected threefold overlap assembled from the selected pairwise and middle pullbacks. -/
noncomputable def chosenTriple (i j k : 𝒰.index) :
    ChosenPullback₃
      (𝒰.chosenOverlap i j) (𝒰.chosenOverlap j k) (𝒰.chosenOverlap i k) :=
  ChosenPullback₃.ofMiddle
    (𝒰.chosenOverlap i j) (𝒰.chosenOverlap j k) (𝒰.chosenOverlap i k)
    (chosenMiddle (𝒰 := 𝒰) i j k) (chosenOuterLift (𝒰 := 𝒰) i j k)

/-- An actual overlap presentation selected from family-local pairwise and triple pullback
assumptions. -/
@[stacks 026B "overlap presentation selected from local pullbacks"]
noncomputable def ofHasOverlaps : 𝒰.OverlapPresentation where
  pairwise := 𝒰.chosenOverlap
  triple := chosenTriple

/-- The pairwise choices of `ofHasOverlaps` are the selected pairwise overlaps. -/
@[simp, stacks 026B "selected overlap presentation pairwise readout"]
theorem ofHasOverlaps_pairwise (i j : 𝒰.index) :
    (ofHasOverlaps (𝒰 := 𝒰)).pairwise i j = 𝒰.chosenOverlap i j := sorry

/-- The triple choices of `ofHasOverlaps` are the explicitly assembled selected triples. -/
@[simp, stacks 026B "selected overlap presentation triple readout"]
theorem ofHasOverlaps_triple (i j k : 𝒰.index) :
    (ofHasOverlaps (𝒰 := 𝒰)).triple i j k = chosenTriple (𝒰 := 𝒰) i j k := sorry

end FamilyLocal

end SemiRepresentableFamily.Over.OverlapPresentation

end CategoryTheory
