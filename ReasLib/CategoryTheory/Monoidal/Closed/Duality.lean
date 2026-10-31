/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.CategoryTheory.Monoidal.Duality.Dualizable
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual

/-!
# Canonical duality maps in braided closed monoidal categories

For an object `X`, its closed-monoidal dual is the internal Hom from `X` to the tensor unit.
This leaf owns the evaluation, tensor/internal-Hom comparison, bidual comparison, and induced map
on morphisms from the tensor unit.  The constructions are independent of rings and sheaves.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe v u

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [BraidedCategory C] [MonoidalClosed C]

/-- The canonical closed-monoidal dual of `X`, namely the internal Hom from `X` to the tensor
unit. -/
abbrev dual (X : C) : C :=
  (ihom X).obj (𝟙_ C)

namespace Dual

/-- Evaluation of the canonical closed-monoidal dual. -/
@[stacks 0FNY "closed-monoidal dual evaluation"]
def evaluation (X : C) : dual X ⊗ X ⟶ 𝟙_ C :=
  (β_ (dual X) X).hom ≫ (ihom.ev X).app (𝟙_ C)

/-- The canonical comparison from tensoring with the closed-monoidal dual to an internal Hom. -/
@[stacks 08I2]
def tensorComparison (X M : C) :
    M ⊗ dual X ⟶ (ihom X).obj M :=
  ((unitIsoSelf M).symm.hom ⊗ₘ 𝟙 (dual X)) ≫
    (β_ ((ihom (𝟙_ C)).obj M) (dual X)).hom ≫
      comp X (𝟙_ C) M

/-- The canonical map from an object to its closed-monoidal bidual. -/
@[stacks 01DS "closed-monoidal bidual map"]
def bidualComparison (X : C) : X ⟶ dual (dual X) :=
  curry (evaluation X)

/-- The map on morphisms from the tensor unit induced by `tensorComparison`. -/
@[stacks 08I1]
def homComparison (X M : C) :
    (𝟙_ C ⟶ M ⊗ dual X) → (X ⟶ M) :=
  fun s => uncurry' (s ≫ tensorComparison X M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison is natural in its target. -/
@[stacks 08I2 "tensor comparison target naturality"]
theorem tensorComparison_natural
    (X : C) {M N : C} (f : M ⟶ N) :
    (f ⊗ₘ 𝟙 (dual X)) ≫ tensorComparison X N =
      tensorComparison X M ≫ (ihom X).map f := by
  have hc : (dual X ◁ (ihom (𝟙_ C)).map f) ≫ comp X (𝟙_ C) N =
      comp X (𝟙_ C) M ≫ (ihom X).map f := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_natural_right]
    simp only [comp_eq, uncurry_curry, compTranspose_eq]
    rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
    dsimp only [Functor.id_obj]
    rw [ihom.ev_naturality]
    simp only [Category.assoc]
  have hu : f ≫ (unitIsoSelf N).symm.hom =
      (unitIsoSelf M).symm.hom ≫ (ihom (𝟙_ C)).map f := by
    exact unitNatIso.hom.naturality f
  simp only [tensorComparison, tensorHom_id,
    BraidedCategory.braiding_naturality_left_assoc, Category.assoc]
  rw [← whiskerLeft_comp_assoc, hu, whiskerLeft_comp_assoc, hc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor comparison is contravariantly natural in the object being dualized. -/
@[stacks 08I2 "tensor comparison source naturality"]
theorem tensorComparison_natural_source
    {X Y : C} (f : X ⟶ Y) (M : C) :
    (M ◁ (pre f).app (𝟙_ C)) ≫ tensorComparison X M =
      tensorComparison Y M ≫ (pre f).app M := by
  have hc : (pre f).app (𝟙_ C) ▷ (ihom (𝟙_ C)).obj M ≫ comp X (𝟙_ C) M =
      comp Y (𝟙_ C) M ≫ (pre f).app M := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_pre_app]
    simp only [comp_eq, uncurry_curry, compTranspose_eq]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
      associator_inv_naturality_left_assoc]
  simp only [tensorComparison, tensorHom_id,
    BraidedCategory.braiding_naturality_left_assoc, Category.assoc]
  rw [BraidedCategory.braiding_naturality_right_assoc, ← whisker_exchange_assoc, hc]

/-- Naturality of the tensor/internal-Hom comparison when its source object is viewed in the
opposite category. -/
theorem tensorComparison_naturality_op
    (M : C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((internalHom (C := C)).flip.obj (𝟙_ C) ⋙ tensorLeft M).map f ≫
        tensorComparison Y.unop M =
      tensorComparison X.unop M ≫
        ((internalHom (C := C)).flip.obj M).map f := by
  exact tensorComparison_natural_source f.unop M

/-- The canonical tensor/internal-Hom comparison, natural in the object being dualized. -/
@[stacks 08I2 "tensor/internal-Hom natural comparison"]
def tensorComparisonNatTrans (M : C) :
    (internalHom (C := C)).flip.obj (𝟙_ C) ⋙ tensorLeft M ⟶
      (internalHom (C := C)).flip.obj M where
  app X := tensorComparison X.unop M
  naturality _ _ f := tensorComparison_naturality_op M f

/-- Uncurrying the bidual comparison recovers dual evaluation. -/
@[simp]
theorem uncurry_bidualComparison (X : C) :
    uncurry (bidualComparison X) = evaluation X := by
  exact uncurry_curry (evaluation X)

/-- Applying `homComparison` amounts to postcomposition with `tensorComparison` followed by
closed-monoidal uncurrying. -/
@[simp]
theorem homComparison_apply
    (X M : C) (s : 𝟙_ C ⟶ M ⊗ dual X) :
    homComparison X M s = uncurry' (s ≫ tensorComparison X M) := rfl

/-- The map on morphisms from the tensor unit is functorial in the target object. -/
@[stacks 08I1 "degree-zero dual comparison naturality"]
theorem homComparison_natural_apply
    (X : C) {M N : C} (f : M ⟶ N) (s : 𝟙_ C ⟶ M ⊗ dual X) :
    homComparison X N (s ≫ (f ⊗ₘ 𝟙 (dual X))) = homComparison X M s ≫ f := by
  simp only [homComparison, Category.assoc, tensorComparison_natural]
  simp only [uncurry']
  rw [← Category.assoc s (tensorComparison X M) ((ihom X).map f),
    uncurry_natural_right, Category.assoc]

section Additive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The canonical comparison on morphisms from the tensor unit is additive. -/
@[stacks 08JD "additivity of the degree-zero dual comparison"]
theorem homComparison_add
    (X M : C) (s t : 𝟙_ C ⟶ M ⊗ dual X) :
    homComparison X M (s + t) = homComparison X M s + homComparison X M t := by
  simp [homComparison, uncurry', uncurry_eq, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The canonical degree-zero dual comparison as an additive homomorphism. -/
@[stacks 08JD "additive degree-zero dual comparison"]
noncomputable abbrev homComparisonAddMonoidHom
    (X M : C) :
    AddMonoidHom (𝟙_ C ⟶ M ⊗ dual X) (X ⟶ M) :=
  AddMonoidHom.mk' (homComparison X M) (homComparison_add X M)

/-- The canonical degree-zero dual comparison as a morphism of `AddCommGrpCat`. -/
@[stacks 08JD "AddCommGrp-valued degree-zero dual comparison"]
noncomputable abbrev homComparisonAddCommGrpHom
    (X M : C) :
    AddCommGrpCat.of (𝟙_ C ⟶ M ⊗ dual X) ⟶ AddCommGrpCat.of (X ⟶ M) :=
  AddCommGrpCat.ofHom (homComparisonAddMonoidHom X M)

end Additive

namespace Pairing

/-- Tensoring two morphisms from the tensor unit gives the top edge of the canonical
dual-evaluation square. -/
def top (M X : C) :
    ((𝟙_ C ⟶ M ⊗ dual X) × (𝟙_ C ⟶ X)) →
      (𝟙_ C ⟶ (M ⊗ dual X) ⊗ X) :=
  fun p ↦ (λ_ (𝟙_ C)).inv ≫ (p.1 ⊗ₘ p.2)

/-- Applying `homComparison` to the first component gives the left edge of the canonical
dual-evaluation square. -/
def left (M X : C) :
    ((𝟙_ C ⟶ M ⊗ dual X) × (𝟙_ C ⟶ X)) →
      ((X ⟶ M) × (𝟙_ C ⟶ X)) :=
  fun p ↦ (homComparison X M p.1, p.2)

/-- Evaluation against the closed-monoidal dual gives the right edge of the canonical
dual-evaluation square. -/
def right (M X : C) :
    (𝟙_ C ⟶ (M ⊗ dual X) ⊗ X) → (𝟙_ C ⟶ M) :=
  fun s ↦
    s ≫ (α_ M (dual X) X).hom ≫
      M ◁ evaluation X ≫ (ρ_ M).hom

/-- Composition gives the bottom edge of the canonical dual-evaluation square. -/
def bottom (M X : C) :
    ((X ⟶ M) × (𝟙_ C ⟶ X)) → (𝟙_ C ⟶ M) :=
  fun p ↦ p.2 ≫ p.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise form of the canonical dual-evaluation square. -/
@[stacks 0FVB "closed-monoidal dual-evaluation pairing"]
theorem commSq_apply
    (M X : C) (s : 𝟙_ C ⟶ M ⊗ dual X) (t : 𝟙_ C ⟶ X) :
    right M X (top M X (s, t)) = bottom M X (left M X (s, t)) := by
  -- Both routes evaluate the dual at `t` before composing with `s`.
  let a : dual X ⟶ 𝟙_ C :=
    (λ_ (dual X)).inv ≫ t ▷ dual X ≫ (ihom.ev X).app (𝟙_ C)
  have hu : 𝟙_ C ◁ (unitIsoSelf M).symm.hom ≫ (ihom.ev (𝟙_ C)).app M =
      (λ_ M).hom := by
    have h := conjugateEquiv_counit (Adjunction.id (C := C))
      (ihom.adjunction (𝟙_ C)) (leftUnitorNatIso C).hom M
    change 𝟙_ C ◁ (unitIsoSelf M).symm.hom ≫ (ihom.ev (𝟙_ C)).app M =
      (λ_ M).hom ≫ 𝟙 M at h
    simpa only [Category.comp_id] using h
  have htop : right M X (top M X (s, t)) = s ≫ M ◁ a ≫ (ρ_ M).hom := by
    dsimp only [right, top]
    simp only [tensorHom_def, Category.assoc]
    rw [unitors_inv_equal, ← rightUnitor_inv_naturality_assoc,
      associator_naturality_right_assoc, ← whiskerLeft_rightUnitor_inv_assoc]
    simp only [evaluation, whiskerLeft_comp, Category.assoc]
    simp only [← whiskerLeft_comp_assoc]
    rw [BraidedCategory.braiding_naturality_right_assoc,
      rightUnitor_inv_braiding_assoc]
  have hbottom : bottom M X (left M X (s, t)) = s ≫ M ◁ a ≫ (ρ_ M).hom := by
    dsimp only [bottom, left, homComparison, uncurry']
    rw [uncurry_natural_left]
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
      ← unitors_inv_equal, ← leftUnitor_inv_naturality_assoc]
    simp only [tensorComparison, tensorHom_id,
      BraidedCategory.braiding_naturality_left_assoc, uncurry_natural_left,
      comp_eq, uncurry_curry, compTranspose_eq]
    rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, ← leftUnitor_inv_naturality_assoc,
      ← leftUnitor_inv_naturality_assoc, leftUnitor_tensor_inv]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
    simp only [Category.assoc]
    change s ≫ (β_ M (dual X)).hom ≫
        dual X ◁ (unitIsoSelf M).symm.hom ≫
        a ▷ (ihom (𝟙_ C)).obj M ≫ (ihom.ev (𝟙_ C)).app M =
      s ≫ M ◁ a ≫ (ρ_ M).hom
    rw [whisker_exchange_assoc, hu,
      ← BraidedCategory.braiding_naturality_right_assoc]
    dsimp only [Functor.id_obj]
    rw [braiding_leftUnitor]
  exact htop.trans hbottom.symm

/-- The tensor product of two morphisms from the tensor unit is compatible with the canonical
map into `X ⟶ M` and evaluation against the closed-monoidal dual of `X`. -/
@[stacks 0FVB "closed-monoidal dual-evaluation square"]
theorem commSq (M X : C) :
    CommSq (C := Type _)
      (TypeCat.ofHom (top M X))
      (TypeCat.ofHom (left M X))
      (TypeCat.ofHom (right M X))
      (TypeCat.ofHom (bottom M X)) := by
  constructor
  apply ConcreteCategory.hom_ext
  intro p
  exact commSq_apply M X p.1 p.2

end Pairing

/-- At `M = X`, the tensor comparison agrees with the canonical tensor-to-endomorphism map. -/
theorem tensorComparison_self (X : C) :
    tensorComparison X X = tensorIhomUnitToEnd X := by
  simp only [tensorComparison, tensorIhomUnitToEnd, tensorHom_id,
    BraidedCategory.braiding_naturality_left_assoc]
  rfl

/-- Invertibility of the canonical tensor-to-endomorphism map implies invertibility of the
self tensor comparison. -/
theorem isIso_tensorComparison_self
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    IsIso (tensorComparison X X) := by
  rw [tensorComparison_self]
  infer_instance

/-- Invertibility of the self tensor comparison implies invertibility of the canonical
tensor-to-endomorphism map. -/
theorem isIso_tensorIhomUnitToEnd
    (X : C) [IsIso (tensorComparison X X)] :
    IsIso (tensorIhomUnitToEnd X) := by
  rw [← tensorComparison_self]
  infer_instance

/-- The source-order canonical exact pairing
`ExactPairing X (dual X)`.  Its coevaluation has target `X ⊗ dual X`, and its evaluation has
source `dual X ⊗ X`. -/
@[stacks 0FPC "closed-monoidal canonical exact pairing", implicit_reducible]
def exactPairing
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    ExactPairing X (dual X) :=
  BraidedCategory.exactPairing_swap (dual X) X

/-- The canonical coevaluation from the tensor unit to an object tensored with its
closed-monoidal dual. -/
@[stacks 0FPC "closed-monoidal canonical coevaluation"]
def coevaluation
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    𝟙_ C ⟶ X ⊗ dual X :=
  curry' (𝟙 X) ≫ inv (tensorIhomUnitToEnd X)

/-- Coevaluation in the source-order canonical exact pairing is `Dual.coevaluation`. -/
@[simp]
theorem exactPairing_coevaluation
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    @ExactPairing.coevaluation' C _ _ X (dual X) (exactPairing X) = coevaluation X := by
  change (curry' (𝟙 X) ≫ inv (tensorIhomUnitToEnd X) ≫
    (β_ X (dual X)).hom) ≫ (β_ X (dual X)).inv = coevaluation X
  simp [coevaluation]

/-- The canonical coevaluation corresponds to the identity under the tensor-to-internal-Hom
comparison. -/
@[reassoc]
theorem coevaluation_comp_tensorComparison
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    coevaluation X ≫ tensorComparison X X = curry' (𝟙 X) := by
  simp [coevaluation, tensorComparison_self]

/-- A map from the tensor unit is the canonical coevaluation exactly when it corresponds to the
identity under the tensor-to-internal-Hom comparison. -/
theorem eq_coevaluation_iff
    (X : C) [IsIso (tensorIhomUnitToEnd X)] (η : 𝟙_ C ⟶ X ⊗ dual X) :
    η = coevaluation X ↔ η ≫ tensorComparison X X = curry' (𝟙 X) := by
  letI := isIso_tensorComparison_self X
  rw [← coevaluation_comp_tensorComparison X, cancel_mono]

/-- The canonical coevaluation is the unique map corresponding to the identity under the
tensor-to-internal-Hom comparison. -/
theorem coevaluation_unique
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    ∃! η : 𝟙_ C ⟶ X ⊗ dual X,
      η ≫ tensorComparison X X = curry' (𝟙 X) := by
  refine ⟨coevaluation X, coevaluation_comp_tensorComparison X, ?_⟩
  intro η hη
  exact (eq_coevaluation_iff X η).2 hη

/-- Evaluation in the source-order canonical exact pairing is `Dual.evaluation`. -/
@[simp]
theorem exactPairing_evaluation
    (X : C) [IsIso (tensorIhomUnitToEnd X)] :
    @ExactPairing.evaluation _ _ _ X (dual X) (exactPairing X) = evaluation X := rfl

/-- The first object of an exact pairing is canonically isomorphic to the closed-monoidal dual
of the second object. -/
def leftDualIso
    {X Y : C} (p : ExactPairing X Y) :
    X ≅ dual Y :=
  p.curryEvaluationIso

/-- The second object of an exact pairing is canonically isomorphic to the closed-monoidal dual
of the first object. -/
@[stacks 0FPA "canonical identification of a chosen dual"]
def rightDualIso
    {X Y : C} (p : ExactPairing X Y) :
    Y ≅ dual X :=
  ExactPairing.curryEvaluationIso
    (@BraidedCategory.exactPairing_swap C _ _ _ X Y p)

end Dual

end CategoryTheory.MonoidalClosed

/- The notation is opt-in because other dualities use the same glyph. -/
scoped[ClosedDual] postfix:max "^∨" => CategoryTheory.MonoidalClosed.dual
