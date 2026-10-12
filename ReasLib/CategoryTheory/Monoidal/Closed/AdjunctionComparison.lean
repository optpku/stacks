/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Adjunction.RelativeCupProduct
public import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Internal-Hom comparison for an adjunction

For braided closed monoidal categories, a tensor comparison for a left adjoint produces a canonical
map from the right adjoint of an internal Hom to the internal Hom of the right-adjoint images.  The
construction is stated at the categorical level so that derived pushforwards are only a later
specialization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe uC uD vC vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]
  [MonoidalClosed D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- The source-side evaluation morphism in a braided closed monoidal category, written in source
tensor order. -/
@[stacks 0B6D "internal-Hom evaluation"]
abbrev derivedInternalHomEvaluation (A B : D) :
    (ihom A).obj B ⊗ A ⟶ B :=
  (β_ ((ihom A).obj B) A).hom ≫ (ihom.ev A).app B

/-- The morphism family underlying a pointwise pullback-tensor comparison. -/
@[stacks 0B6D "pullback tensor comparison"]
def derivedPullbackTensorComparison
    (pullbackTensorIso :
      ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B) :
    ∀ A B : C,
      L.obj (((curriedTensor C).obj A).obj B) ⟶
        ((curriedTensor D).obj (L.obj A)).obj (L.obj B) :=
  fun A B ↦ (pullbackTensorIso A B).hom

/-- The tensor-side map whose braided transpose defines the internal-Hom comparison. -/
@[stacks 0B6D "internal-Hom comparison adjoint map"]
noncomputable def derivedPushforwardInternalHomComparisonAdjointMap
    (adj : L ⊣ R)
    (pullbackTensorIso :
      ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (A B : D) :
    R.obj ((ihom A).obj B) ⊗ R.obj A ⟶ R.obj B :=
  adj.relativeDerivedCupProduct
      (curriedTensor C) (curriedTensor D)
      (derivedPullbackTensorComparison (L := L) pullbackTensorIso)
      ((ihom A).obj B) A ≫
    R.map (derivedInternalHomEvaluation A B)

/-- The canonical internal-Hom comparison associated to an adjunction and a pullback-tensor
comparison. -/
@[stacks 0B6D "derived pushforward internal-Hom comparison"]
noncomputable def derivedPushforwardInternalHomComparison
    (adj : L ⊣ R)
    (pullbackTensorIso :
      ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (A B : D) :
    R.obj ((ihom A).obj B) ⟶ (ihom (R.obj A)).obj (R.obj B) :=
  braidedHomEquiv
      (R.obj ((ihom A).obj B)) (R.obj A) (R.obj B)
      (derivedPushforwardInternalHomComparisonAdjointMap adj pullbackTensorIso A B)

/-- The internal-Hom comparison transposes to the relative cup product followed by the
right-adjoint image of evaluation. -/
@[stacks 0B6D "derived pushforward internal-Hom comparison specification"]
theorem derivedPushforwardInternalHomComparison_spec
    (adj : L ⊣ R)
    (pullbackTensorIso :
      ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (A B : D) :
    (braidedHomEquiv
        (R.obj ((ihom A).obj B)) (R.obj A) (R.obj B)).symm
      (derivedPushforwardInternalHomComparison adj pullbackTensorIso A B) =
      adj.relativeDerivedCupProduct
          (curriedTensor C) (curriedTensor D)
          (derivedPullbackTensorComparison (L := L) pullbackTensorIso)
          ((ihom A).obj B) A ≫
        R.map (derivedInternalHomEvaluation A B) := sorry

/- The square form is the downstream-facing evaluation API.  It keeps the mate construction
behind a single `CommSq`, so later arguments can compose it without unfolding `braidedHomEquiv`. -/
/-- The internal-Hom comparison is compatible with evaluation.  The top edge is the relative
cup product followed by `R.map` of the source evaluation, the left edge is the comparison map
tensored with the identity, and the bottom edge is evaluation in the target category. -/
@[stacks 0G7A "internal-Hom comparison and evaluation"]
theorem derivedPushforwardInternalHomComparison_evaluation_commSq
    (adj : L ⊣ R)
    (pullbackTensorIso :
      ∀ A B : C, L.obj (A ⊗ B) ≅ L.obj A ⊗ L.obj B)
    (A B : D) :
    CommSq
      (derivedPushforwardInternalHomComparisonAdjointMap adj pullbackTensorIso A B)
      (derivedPushforwardInternalHomComparison adj pullbackTensorIso A B ⊗ₘ
        𝟙 (R.obj A))
      (𝟙 (R.obj B))
      ((β_ ((ihom (R.obj A)).obj (R.obj B)) (R.obj A)).hom ≫
        (ihom.ev (R.obj A)).app (R.obj B)) := sorry

end CategoryTheory.Adjunction
