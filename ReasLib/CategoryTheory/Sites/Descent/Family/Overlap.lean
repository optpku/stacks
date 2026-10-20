module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Family.Overlap.Basic

/-!
# Chosen overlap presentations for fixed-target families

For a family `𝒰 : SemiRepresentableFamily.Over U` of morphisms targeting a common object `U`,
the overlap objects `Uᵢ ×[U] Uⱼ` and triple overlaps `Uᵢ ×[U] Uⱼ ×[U] Uₖ` are the
fiber products witnessing the descent conditions. The underlying pairwise overlap objects and
their universal-property API are owned by
`CategoryTheory.Sites.Family.Overlap.Basic`. This descent-specific leaf provides:

* `HasTripleOverlaps` for the remaining family-local existence assumption.
* `OverlapPresentation` for bridges that must retain explicit pairwise and triple choices.

## Main declarations

* `SemiRepresentableFamily.Over.OverlapPresentation` — explicit descent pullback data.
* `SemiRepresentableFamily.Over.HasTripleOverlaps` — local existence of threefold overlaps.
-/

@[expose] public section

noncomputable section

universe w v₁ u₁

namespace CategoryTheory

open Functor Limits
open SemiRepresentableFamily.Over

variable {C : Type u₁} [Category.{v₁} C]

namespace SemiRepresentableFamily.Over

variable {U : C} (𝒰 : SemiRepresentableFamily.Over U)

/-! ## Existence of overlaps -/

/-- An explicit choice of all pairwise and triple overlaps of a fixed-target family.

Unlike the proposition-valued existence conditions used below, this structure owns the pullback
objects and projections.  It is therefore the appropriate input for constructions whose result
depends on a chosen presentation. -/
@[stacks 026B "chosen pairwise and triple overlaps"]
structure OverlapPresentation where
  /-- The chosen pullback of every pair of family members. -/
  pairwise (i j : 𝒰.index) : ChosenPullback (𝒰.obj i).hom (𝒰.obj j).hom
  /-- A chosen threefold pullback compatible with the three pairwise choices. -/
  triple (i j k : 𝒰.index) :
    ChosenPullback₃ (pairwise i j) (pairwise j k) (pairwise i k)

namespace OverlapPresentation

variable {𝒰 : SemiRepresentableFamily.Over U}
variable (P : 𝒰.OverlapPresentation)

/-- The pairwise overlap object selected by an overlap presentation. -/
abbrev overlap (i j : 𝒰.index) : C :=
  (P.pairwise i j).pullback

/-- The first projection from a pairwise overlap selected by a presentation. -/
abbrev fst (i j : 𝒰.index) : P.overlap i j ⟶ (𝒰.obj i).left :=
  (P.pairwise i j).p₁

/-- The second projection from a pairwise overlap selected by a presentation. -/
abbrev snd (i j : 𝒰.index) : P.overlap i j ⟶ (𝒰.obj j).left :=
  (P.pairwise i j).p₂

/-- The common map from a presented pairwise overlap to the target of the family. -/
abbrev overlapMap (i j : 𝒰.index) : P.overlap i j ⟶ U :=
  (P.pairwise i j).p

/-- The two projections of a presented overlap have the same composite to the family target. -/
theorem fst_hom_eq_snd_hom (i j : 𝒰.index) :
    P.fst i j ≫ (𝒰.obj i).hom = P.snd i j ≫ (𝒰.obj j).hom := sorry

/-- The first projection of a presented overlap factors through its common target map. -/
theorem fst_hom (i j : 𝒰.index) :
    P.fst i j ≫ (𝒰.obj i).hom = P.overlapMap i j := sorry

/-- The second projection of a presented overlap factors through its common target map. -/
theorem snd_hom (i j : 𝒰.index) :
    P.snd i j ≫ (𝒰.obj j).hom = P.overlapMap i j := sorry

end OverlapPresentation

/-- The pairwise member of the overlap presentation selected from ambient pullbacks.  This is a
source-facing bridge, not a second pairwise-pullback owner. -/
@[stacks 026B "pairwise overlaps selected from ambient pullbacks"]
noncomputable def OverlapPresentation.pairwiseOfPullbacks [HasPullbacks C]
    (i j : 𝒰.index) : ChosenPullback (𝒰.obj i).hom (𝒰.obj j).hom :=
  ChosenPullback.ofHasPullback (𝒰.obj i).hom (𝒰.obj j).hom

/-- Ambient pullbacks ensure that the threefold overlap extending the selected pairwise pullbacks
exists. The statement deliberately does not choose its outer lift. -/
@[stacks 026B "triple overlap existence from ambient pullbacks"]
theorem OverlapPresentation.tripleNonemptyOfPullbacks [HasPullbacks C]
    (i j k : 𝒰.index) :
    Nonempty
      (ChosenPullback₃ (OverlapPresentation.pairwiseOfPullbacks 𝒰 i j)
        (OverlapPresentation.pairwiseOfPullbacks 𝒰 j k)
        (OverlapPresentation.pairwiseOfPullbacks 𝒰 i k)) := sorry

section Pairwise

variable [𝒰.toPresieve.HasPairwisePullbacks]

/-! ## Triple-overlap existence and presentations -/

/-- Every triple of members has the middle pullback needed to form its threefold overlap.
Unlike `[HasPullbacks C]`, this is a local condition on one fixed-target family and its chosen
pairwise overlaps. -/
@[stacks 026B "family-local triple-overlap existence"]
class HasTripleOverlaps : Prop where
  /-- The pullback completing the threefold overlap of `i`, `j`, and `k`. -/
  triple (i j k : 𝒰.index) : HasPullback (𝒰.snd i j) (𝒰.fst j k)

/-- The middle pullback supplied by a triple-overlap assumption. -/
instance triple_hasPullback [𝒰.HasTripleOverlaps] (i j k : 𝒰.index) :
    HasPullback (𝒰.snd i j) (𝒰.fst j k) := sorry

/-- A category with all pullbacks supplies the triple overlaps of every fixed-target family. -/
instance hasTripleOverlaps_of_hasPullbacks [HasPullbacks C] :
    𝒰.HasTripleOverlaps := sorry

/-- Build an overlap presentation from the canonical selected pairwise overlaps and explicit
threefold-overlap data. The outer lift morphisms remain supplied by the caller. -/
@[stacks 026B "overlap presentation from chosen triples"]
def OverlapPresentation.ofChosenTriples
    (triple : ∀ i j k : 𝒰.index,
      ChosenPullback₃ (𝒰.chosenOverlap i j) (𝒰.chosenOverlap j k)
        (𝒰.chosenOverlap i k)) :
    𝒰.OverlapPresentation where
  pairwise := 𝒰.chosenOverlap
  triple := triple

/-- Family-local pairwise and triple pullback assumptions imply that an explicit overlap
presentation exists. This proposition leaves the choice of outer lift morphisms to a later proof
or to explicit caller data. -/
@[stacks 026B "overlap presentation existence from local pullbacks"]
theorem OverlapPresentation.nonemptyOfHasOverlaps [𝒰.HasTripleOverlaps] :
    Nonempty 𝒰.OverlapPresentation := sorry

end Pairwise

/-- A category with pullbacks admits an overlap presentation for every fixed-target family. -/
@[stacks 026B "overlap presentation existence from ambient pullbacks"]
theorem OverlapPresentation.nonemptyOfPullbacks [HasPullbacks C] :
    Nonempty 𝒰.OverlapPresentation := sorry

end SemiRepresentableFamily.Over

end CategoryTheory

/- Axiom audit: `ofChosenTriples` only assembles caller-supplied threefold overlap data with the
canonical pairwise choices; no proof placeholder determines a morphism. -/
