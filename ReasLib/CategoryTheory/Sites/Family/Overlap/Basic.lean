module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.ChosenPullback.Canonical
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Pairwise overlaps of fixed-target families

This file owns the chosen pairwise overlaps of a fixed-target family independently of descent
data.  It provides the overlap object, its projections and common target map, the pullback
universal property, and the canonical diagonal and symmetry maps.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]
variable {U : C} (𝒰 : SemiRepresentableFamily.Over.{w} U)
variable [𝒰.toPresieve.HasPairwisePullbacks]

/-- The chosen pairwise overlap of two members of a fixed-target family. -/
@[stacks 026B "chosen pairwise overlap", stacks 026D "canonical overlap owner"]
noncomputable abbrev chosenOverlap (i j : 𝒰.index) :
    ChosenPullback (𝒰.obj i).hom (𝒰.obj j).hom :=
  ChosenPullback.ofHasPullbackProof
    (Presieve.HasPairwisePullbacks.has_pullbacks
      (R := 𝒰.toPresieve) (Presieve.ofArrows.mk i) (Presieve.ofArrows.mk j))

/-- The pairwise overlap `Uᵢ ×[U] Uⱼ`. -/
@[stacks 026B "pairwise overlap object", stacks 026D "canonical overlap object"]
abbrev Overlap (i j : 𝒰.index) : C := (𝒰.chosenOverlap i j).pullback

/-- First projection `Uᵢ ×[U] Uⱼ ⟶ Uᵢ`. -/
@[stacks 026B "first overlap projection", stacks 026D "canonical overlap first projection"]
abbrev fst (i j : 𝒰.index) : 𝒰.Overlap i j ⟶ (𝒰.obj i).left :=
  (𝒰.chosenOverlap i j).p₁

/-- Second projection `Uᵢ ×[U] Uⱼ ⟶ Uⱼ`. -/
@[stacks 026B "second overlap projection", stacks 026D "canonical overlap second projection"]
abbrev snd (i j : 𝒰.index) : 𝒰.Overlap i j ⟶ (𝒰.obj j).left :=
  (𝒰.chosenOverlap i j).p₂

/-- The two projections compose to the same map to `U`. -/
@[reassoc, stacks 026B "overlap compatibility", stacks 026D "overlap compatibility readout"]
theorem fst_hom_eq_snd_hom (i j : 𝒰.index) :
    𝒰.fst i j ≫ (𝒰.obj i).hom = 𝒰.snd i j ≫ (𝒰.obj j).hom := sorry

/-- The common composite from a pairwise overlap to the target of the family. -/
@[stacks 026B "overlap target map", stacks 026D "canonical overlap target map"]
abbrev overlapMap (i j : 𝒰.index) : 𝒰.Overlap i j ⟶ U :=
  (𝒰.chosenOverlap i j).p

/-- The first projection factors through the chosen overlap map. -/
@[reassoc, stacks 026B "first overlap factorization", stacks 026D "canonical first factorization"]
theorem fst_hom (i j : 𝒰.index) :
    𝒰.fst i j ≫ (𝒰.obj i).hom = 𝒰.overlapMap i j := sorry

/-- The second projection factors through the chosen overlap map. -/
@[reassoc, stacks 026B "second overlap factorization", stacks 026D "canonical second factorization"]
theorem snd_hom (i j : 𝒰.index) :
    𝒰.snd i j ≫ (𝒰.obj j).hom = 𝒰.overlapMap i j := sorry

/-- The universal morphism to an overlap induced by two compatible component morphisms. -/
@[stacks 026B "overlap universal lift"]
noncomputable def Overlap.lift {Z : C} (i j : 𝒰.index)
    (g₁ : Z ⟶ (𝒰.obj i).left) (g₂ : Z ⟶ (𝒰.obj j).left)
    (h : g₁ ≫ (𝒰.obj i).hom = g₂ ≫ (𝒰.obj j).hom) :
    Z ⟶ 𝒰.Overlap i j :=
  (𝒰.chosenOverlap i j).isPullback.lift g₁ g₂ h

/-- The first projection of the canonical overlap lift is the supplied first morphism. -/
@[reassoc, simp, stacks 026B "overlap lift first projection"]
theorem Overlap.lift_fst {Z : C} (i j : 𝒰.index)
    (g₁ : Z ⟶ (𝒰.obj i).left) (g₂ : Z ⟶ (𝒰.obj j).left)
    (h : g₁ ≫ (𝒰.obj i).hom = g₂ ≫ (𝒰.obj j).hom) :
    Overlap.lift 𝒰 i j g₁ g₂ h ≫ 𝒰.fst i j = g₁ := sorry

/-- The second projection of the canonical overlap lift is the supplied second morphism. -/
@[reassoc, simp, stacks 026B "overlap lift second projection"]
theorem Overlap.lift_snd {Z : C} (i j : 𝒰.index)
    (g₁ : Z ⟶ (𝒰.obj i).left) (g₂ : Z ⟶ (𝒰.obj j).left)
    (h : g₁ ≫ (𝒰.obj i).hom = g₂ ≫ (𝒰.obj j).hom) :
    Overlap.lift 𝒰 i j g₁ g₂ h ≫ 𝒰.snd i j = g₂ := sorry

/-- Any morphism to an overlap is determined by its two projections. -/
@[stacks 026B "overlap lift uniqueness"]
theorem Overlap.lift_unique {Z : C} (i j : 𝒰.index)
    (g₁ : Z ⟶ (𝒰.obj i).left) (g₂ : Z ⟶ (𝒰.obj j).left)
    (h : g₁ ≫ (𝒰.obj i).hom = g₂ ≫ (𝒰.obj j).hom)
    (f : Z ⟶ 𝒰.Overlap i j) (hf₁ : f ≫ 𝒰.fst i j = g₁) (hf₂ : f ≫ 𝒰.snd i j = g₂) :
    f = Overlap.lift 𝒰 i j g₁ g₂ h := sorry

/-- The two identity maps define a compatible cone over a self-overlap. -/
@[stacks 026B "overlap diagonal compatibility"]
theorem Overlap.diag_condition (i : 𝒰.index) :
    𝟙 (𝒰.obj i).left ≫ (𝒰.obj i).hom =
      𝟙 (𝒰.obj i).left ≫ (𝒰.obj i).hom := sorry

/-- The diagonal morphism `Uᵢ ⟶ Uᵢ ×[U] Uᵢ`. -/
@[stacks 026B "overlap diagonal"]
def diag (i : 𝒰.index) : (𝒰.obj i).left ⟶ 𝒰.Overlap i i :=
  Overlap.lift 𝒰 i i (𝟙 _) (𝟙 _) (Overlap.diag_condition 𝒰 i)

/-- The overlap diagonal followed by the first projection is the identity. -/
@[reassoc, simp, stacks 026B "overlap diagonal first projection"]
theorem diag_fst (i : 𝒰.index) : 𝒰.diag i ≫ 𝒰.fst i i = 𝟙 _ := sorry

/-- The overlap diagonal followed by the second projection is the identity. -/
@[reassoc, simp, stacks 026B "overlap diagonal second projection"]
theorem diag_snd (i : 𝒰.index) : 𝒰.diag i ≫ 𝒰.snd i i = 𝟙 _ := sorry

/-- The symmetry morphism `Uᵢ ×[U] Uⱼ ⟶ Uⱼ ×[U] Uᵢ`. -/
@[stacks 026B "overlap symmetry"]
def swap (i j : 𝒰.index) : 𝒰.Overlap i j ⟶ 𝒰.Overlap j i :=
  (𝒰.chosenOverlap j i).isPullback.lift (𝒰.snd i j) (𝒰.fst i j)
    (𝒰.chosenOverlap i j).condition.symm

/-- The overlap symmetry exchanges its first projection with the second projection. -/
@[reassoc, simp, stacks 026B "overlap symmetry first projection"]
theorem swap_fst (i j : 𝒰.index) :
    𝒰.swap i j ≫ 𝒰.fst j i = 𝒰.snd i j := sorry

/-- The overlap symmetry exchanges its second projection with the first projection. -/
@[reassoc, simp, stacks 026B "overlap symmetry second projection"]
theorem swap_snd (i j : 𝒰.index) :
    𝒰.swap i j ≫ 𝒰.snd j i = 𝒰.fst i j := sorry

/-- Applying overlap symmetry twice is the identity. -/
@[stacks 026B "involutivity of overlap symmetry"]
theorem swap_swap (i j : 𝒰.index) :
    𝒰.swap i j ≫ 𝒰.swap j i = 𝟙 _ := sorry

/-- The overlap symmetry morphism is an isomorphism. -/
@[stacks 026B "overlap symmetry isomorphism"]
instance swap_isIso (i j : 𝒰.index) : IsIso (𝒰.swap i j) := sorry

/-- The overlap diagonal is a monomorphism. -/
@[stacks 026B "overlap diagonal monomorphism"]
instance diag_mono (i : 𝒰.index) : Mono (𝒰.diag i) := sorry

end SemiRepresentableFamily.Over

end CategoryTheory
