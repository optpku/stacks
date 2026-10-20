/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.CategoryTheory.Monoidal.Duality.Adjunction

/-!
# Comparison API for exact pairings

This leaf records pairing-preserving comparison isomorphisms, uniqueness of specified left and
right duals, and the computation of the two constructions in `Duality.Basic` on explicit data.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false

namespace ExactPairing

/-- An isomorphism between two right duals of the same object preserves the coevaluation and
evaluation morphisms. -/
def RightDualIso {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂)
    (i : Y₁ ≅ Y₂) : Prop :=
  p₁.coevaluation' ≫ X ◁ i.hom = p₂.coevaluation' ∧
    i.hom ▷ X ≫ p₂.evaluation' = p₁.evaluation'

/-- The defining equations for an isomorphism of right-dual pairings. -/
theorem rightDualIso_iff {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁)
    (p₂ : ExactPairing X Y₂) (i : Y₁ ≅ Y₂) :
    RightDualIso p₁ p₂ i ↔
      p₁.coevaluation' ≫ X ◁ i.hom = p₂.coevaluation' ∧
        i.hom ▷ X ≫ p₂.evaluation' = p₁.evaluation' := Iff.rfl

/-- A right-dual isomorphism preserves coevaluation. -/
theorem RightDualIso.coevaluation {X Y₁ Y₂ : C}
    {p₁ : ExactPairing X Y₁} {p₂ : ExactPairing X Y₂} {i : Y₁ ≅ Y₂}
    (h : RightDualIso p₁ p₂ i) :
    p₁.coevaluation' ≫ X ◁ i.hom = p₂.coevaluation' := h.1

/-- A right-dual isomorphism preserves evaluation. -/
theorem RightDualIso.evaluation {X Y₁ Y₂ : C}
    {p₁ : ExactPairing X Y₁} {p₂ : ExactPairing X Y₂} {i : Y₁ ≅ Y₂}
    (h : RightDualIso p₁ p₂ i) :
    i.hom ▷ X ≫ p₂.evaluation' = p₁.evaluation' := h.2

/-- The canonical isomorphism between right duals preserves both pairing maps. -/
@[stacks 0FFR "canonical right-dual isomorphism preserves the pairing"]
theorem rightDualIso.isCompatible {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    RightDualIso p₁ p₂ (rightDualIso p₁ p₂) := by
  -- Local instance justification (noncanonical choice): the theorem compares the two explicitly supplied pairings `p₁` and `p₂`.
  letI : ExactPairing X Y₁ := p₁
  -- Local instance justification (noncanonical choice): the theorem compares the two explicitly supplied pairings `p₁` and `p₂`.
  letI : ExactPairing X Y₂ := p₂
  constructor
  · change η_ X Y₁ ≫ X ◁ (rightDualIso p₁ p₂).hom = η_ X Y₂
    rw [rightDualIso]
    simpa using
      (@coevaluation_comp_rightAdjointMate C _ _ X X
        ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X))
  · change (rightDualIso p₁ p₂).hom ▷ X ≫ ε_ X Y₂ = ε_ X Y₁
    rw [rightDualIso]
    simpa using
      (@rightAdjointMate_comp_evaluation C _ _ X X
        ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X))

/-- Any pairing-preserving isomorphism between right duals is the canonical one. -/
@[stacks 0FFR "uniqueness of the pairing-preserving right-dual isomorphism"]
theorem rightDualIso.eq_of_compatible {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) (i : Y₁ ≅ Y₂)
    (hi : RightDualIso p₁ p₂ i) :
    i = rightDualIso p₁ p₂ := by
  -- Local instance justification (noncanonical choice): the mate computation must use the explicitly supplied pairing `p₂`.
  letI : ExactPairing X Y₂ := p₂
  ext
  apply (cancel_mono (λ_ Y₂).inv).1
  have h_i := @tensorRightHomEquiv_whiskerRight_comp_evaluation
    C _ _ X Y₁ ⟨Y₂⟩ i.hom
  have h_can := @tensorRightHomEquiv_whiskerRight_comp_evaluation
    C _ _ X Y₁ ⟨Y₂⟩ (rightDualIso p₁ p₂).hom
  change
    (tensorRightHomEquiv Y₁ X Y₂ (𝟙_ C))
        (i.hom ▷ X ≫ p₂.evaluation') = i.hom ≫ (λ_ Y₂).inv at h_i
  change
    (tensorRightHomEquiv Y₁ X Y₂ (𝟙_ C))
        ((rightDualIso p₁ p₂).hom ▷ X ≫ p₂.evaluation') =
      (rightDualIso p₁ p₂).hom ≫ (λ_ Y₂).inv at h_can
  rw [← h_i, ← h_can, hi.2, (rightDualIso.isCompatible p₁ p₂).2]

/-- A right dual is unique up to a unique isomorphism preserving the pairing maps. -/
@[stacks 0FFR "uniqueness of right duals with pairing"]
theorem rightDualIso.isUnique {X Y₁ Y₂ : C}
    (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    RightDualIso p₁ p₂ (rightDualIso p₁ p₂) ∧
      ∀ i : Y₁ ≅ Y₂, RightDualIso p₁ p₂ i → i = rightDualIso p₁ p₂ :=
  ⟨rightDualIso.isCompatible p₁ p₂, rightDualIso.eq_of_compatible p₁ p₂⟩

/-- An isomorphism between two left duals of the same object preserves the coevaluation and
evaluation morphisms. -/
def LeftDualIso {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y)
    (i : X₁ ≅ X₂) : Prop :=
  p₁.coevaluation' ≫ i.hom ▷ Y = p₂.coevaluation' ∧
    Y ◁ i.hom ≫ p₂.evaluation' = p₁.evaluation'

/-- The defining equations for an isomorphism of left-dual pairings. -/
theorem leftDualIso_iff {X₁ X₂ Y : C} (p₁ : ExactPairing X₁ Y)
    (p₂ : ExactPairing X₂ Y) (i : X₁ ≅ X₂) :
    LeftDualIso p₁ p₂ i ↔
      p₁.coevaluation' ≫ i.hom ▷ Y = p₂.coevaluation' ∧
        Y ◁ i.hom ≫ p₂.evaluation' = p₁.evaluation' := Iff.rfl

/-- A left-dual isomorphism preserves coevaluation. -/
theorem LeftDualIso.coevaluation {X₁ X₂ Y : C}
    {p₁ : ExactPairing X₁ Y} {p₂ : ExactPairing X₂ Y} {i : X₁ ≅ X₂}
    (h : LeftDualIso p₁ p₂ i) :
    p₁.coevaluation' ≫ i.hom ▷ Y = p₂.coevaluation' := h.1

/-- A left-dual isomorphism preserves evaluation. -/
theorem LeftDualIso.evaluation {X₁ X₂ Y : C}
    {p₁ : ExactPairing X₁ Y} {p₂ : ExactPairing X₂ Y} {i : X₁ ≅ X₂}
    (h : LeftDualIso p₁ p₂ i) :
    Y ◁ i.hom ≫ p₂.evaluation' = p₁.evaluation' := h.2

/-- The canonical isomorphism between left duals preserves both pairing maps. -/
@[stacks 0FFR "canonical left-dual isomorphism preserves the pairing"]
theorem leftDualIso.isCompatible {X₁ X₂ Y : C}
    (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    LeftDualIso p₁ p₂ (leftDualIso p₁ p₂) := by
  -- Local instance justification (noncanonical choice): the theorem compares the two explicitly supplied pairings `p₁` and `p₂`.
  letI : ExactPairing X₁ Y := p₁
  -- Local instance justification (noncanonical choice): the theorem compares the two explicitly supplied pairings `p₁` and `p₂`.
  letI : ExactPairing X₂ Y := p₂
  constructor
  · change η_ X₁ Y ≫ (leftDualIso p₁ p₂).hom ▷ Y = η_ X₂ Y
    rw [leftDualIso]
    simpa using
      (@coevaluation_comp_leftAdjointMate C _ _ Y Y
        ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y))
  · change Y ◁ (leftDualIso p₁ p₂).hom ≫ ε_ X₂ Y = ε_ X₁ Y
    rw [leftDualIso]
    simpa using
      (@leftAdjointMate_comp_evaluation C _ _ Y Y
        ⟨X₂⟩ ⟨X₁⟩ (𝟙 Y))

/-- Any pairing-preserving isomorphism between left duals is the canonical one. -/
@[stacks 0FFR "uniqueness of the pairing-preserving left-dual isomorphism"]
theorem leftDualIso.eq_of_compatible {X₁ X₂ Y : C}
    (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) (i : X₁ ≅ X₂)
    (hi : LeftDualIso p₁ p₂ i) :
    i = leftDualIso p₁ p₂ := by
  -- Local instance justification (noncanonical choice): the mate computation must use the explicitly supplied pairing `p₂`.
  letI : ExactPairing X₂ Y := p₂
  ext
  apply (cancel_mono (ρ_ X₂).inv).1
  have h_i := @tensorLeftHomEquiv_whiskerLeft_comp_evaluation
    C _ _ X₁ Y ⟨X₂⟩ i.hom
  have h_can := @tensorLeftHomEquiv_whiskerLeft_comp_evaluation
    C _ _ X₁ Y ⟨X₂⟩ (leftDualIso p₁ p₂).hom
  change
    (tensorLeftHomEquiv X₁ X₂ Y (𝟙_ C))
        (Y ◁ i.hom ≫ p₂.evaluation') = i.hom ≫ (ρ_ X₂).inv at h_i
  change
    (tensorLeftHomEquiv X₁ X₂ Y (𝟙_ C))
        (Y ◁ (leftDualIso p₁ p₂).hom ≫ p₂.evaluation') =
      (leftDualIso p₁ p₂).hom ≫ (ρ_ X₂).inv at h_can
  rw [← h_i, ← h_can, hi.2, (leftDualIso.isCompatible p₁ p₂).2]

/-- A left dual is unique up to a unique isomorphism preserving the pairing maps. -/
@[stacks 0FFR "uniqueness of left duals with pairing"]
theorem leftDualIso.isUnique {X₁ X₂ Y : C}
    (p₁ : ExactPairing X₁ Y) (p₂ : ExactPairing X₂ Y) :
    LeftDualIso p₁ p₂ (leftDualIso p₁ p₂) ∧
      ∀ i : X₁ ≅ X₂, LeftDualIso p₁ p₂ i → i = leftDualIso p₁ p₂ :=
  ⟨leftDualIso.isCompatible p₁ p₂, leftDualIso.eq_of_compatible p₁ p₂⟩

end ExactPairing

/-- The tensor-right adjunction attached to explicit exact-pairing data is compatible with
tensoring on the left. -/
@[stacks 0FFR "compatibility of an explicit tensor-right adjunction"]
theorem ExactPairing.tensorRightAdjunction.compatibleWithLeftTensoring
    {X Y : C} (p : ExactPairing X Y) :
    p.tensorRightAdjunction.CompatibleWithLeftTensoring := by
  intro W Z Z' f
  rw [ExactPairing.tensorRightAdjunction]
  rw [CategoryTheory.tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change
    (tensorRightHomEquiv (W ⊗ Z') X Y (W ⊗ Z))
        ((α_ W Z' X).hom ≫ W ◁ f) =
      W ◁ (tensorRightHomEquiv Z' X Y Z) f ≫ (α_ W Z Y).inv
  apply (tensorRightHomEquiv (W ⊗ Z') X Y (W ⊗ Z)).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [← id_tensorHom W f,
    ← id_tensorHom W ((tensorRightHomEquiv Z' X Y Z) f)]
  rw [tensorRightHomEquiv_tensor
    (f := tensorRightHomEquiv Z' X Y Z f) (g := 𝟙 W)]
  rw [Equiv.symm_apply_apply]

/-- The canonical tensor-right adjunction of an exact pairing is compatible with tensoring on
the left. -/
@[stacks 0FFR "compatibility of the canonical tensor-right adjunction"]
theorem ExactPairing.compatibleWithLeftTensoring
    (X Y : C) [ExactPairing X Y] :
    (CategoryTheory.tensorRightAdjunction X Y).CompatibleWithLeftTensoring := by
  simpa [ExactPairing.tensorRightAdjunction] using
    (ExactPairing.tensorRightAdjunction.compatibleWithLeftTensoring
      (inferInstance : ExactPairing X Y))

namespace ExactPairing.tensorRightAdjunction

/-- Reconstructing coevaluation from the tensor-right adjunction of an explicit pairing returns
the original coevaluation map. -/
@[stacks 0FFR "tensor-right adjunction coevaluation computation", simp]
theorem tensorRightCoevaluation {X Y : C}
    (p : ExactPairing X Y) :
    p.tensorRightAdjunction.tensorRightCoevaluation = p.coevaluation' := by
  rw [Adjunction.tensorRightCoevaluation, ExactPairing.tensorRightAdjunction]
  rw [CategoryTheory.tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change
    (ρ_ (𝟙_ C)).inv ≫ (𝟙_ C) ◁ p.coevaluation' ≫
      (α_ (𝟙_ C) X Y).inv ≫ (λ_ X).hom ▷ Y = p.coevaluation'
  monoidal

/-- Reconstructing evaluation from the tensor-right adjunction of an explicit pairing returns
the original evaluation map. -/
@[stacks 0FFR "tensor-right adjunction evaluation computation", simp]
theorem tensorRightEvaluation {X Y : C}
    (p : ExactPairing X Y) :
    p.tensorRightAdjunction.tensorRightEvaluation = p.evaluation' := by
  rw [Adjunction.tensorRightEvaluation, ExactPairing.tensorRightAdjunction]
  rw [CategoryTheory.tensorRightAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change
    (λ_ Y).inv ▷ X ≫ (α_ (𝟙_ C) Y X).hom ≫
      (𝟙_ C) ◁ p.evaluation' ≫ (ρ_ (𝟙_ C)).hom = p.evaluation'
  monoidal

namespace toExactPairing

/-- The coevaluation field after converting an explicit pairing to its tensor-right adjunction
and back is the original coevaluation. -/
@[stacks 0FFR "tensor-right adjunction round-trip coevaluation", simp]
theorem coevaluation' {X Y : C}
    (p : ExactPairing X Y) :
    (p.tensorRightAdjunction.toExactPairing
      (ExactPairing.tensorRightAdjunction.compatibleWithLeftTensoring p)).coevaluation' =
      p.coevaluation' := by
  rw [Adjunction.toExactPairing_coevaluation', tensorRightCoevaluation]

/-- The evaluation field after converting an explicit pairing to its tensor-right adjunction
and back is the original evaluation. -/
@[stacks 0FFR "tensor-right adjunction round-trip evaluation", simp]
theorem evaluation' {X Y : C}
    (p : ExactPairing X Y) :
    (p.tensorRightAdjunction.toExactPairing
      (ExactPairing.tensorRightAdjunction.compatibleWithLeftTensoring p)).evaluation' =
      p.evaluation' := by
  rw [Adjunction.toExactPairing_evaluation', tensorRightEvaluation]

end toExactPairing

end ExactPairing.tensorRightAdjunction

/-- An object is a right dual of another exactly when the corresponding tensor-right functors
admit a tensor-compatible adjunction. -/
@[stacks 0FFR "left duals as tensor-compatible right adjoints"]
theorem ExactPairing.nonempty_iff_exists_compatibleAdjunction (X Y : C) :
    Nonempty (ExactPairing X Y) ↔
      ∃ adj : tensorRight X ⊣ tensorRight Y, adj.CompatibleWithLeftTensoring := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.tensorRightAdjunction,
      ExactPairing.tensorRightAdjunction.compatibleWithLeftTensoring p⟩
  · rintro ⟨adj, hcompat⟩
    exact ⟨adj.toExactPairing hcompat⟩

namespace ExactPairing

/-- The canonical comparison from a specified left dual to the internal Hom into the tensor
unit. Its data comes from uniqueness of right adjoints, rather than from choosing an inverse to
the curried evaluation map. -/
@[stacks 0FNZ "(2), comparison isomorphism"]
noncomputable def curryEvaluationIso {X Y : C} [Closed Y]
    (p : ExactPairing X Y) :
    X ≅ (ihom Y).obj (𝟙_ C) :=
  (ρ_ X).symm ≪≫
    (Adjunction.rightAdjointUniq p.tensorLeftAdjunction (ihom.adjunction Y)).app (𝟙_ C)

/-- The forward map of the canonical comparison is the curried evaluation of the exact
pairing. -/
@[stacks 0FNZ "(2)"]
theorem curryEvaluationIso_hom {X Y : C} [Closed Y]
    (p : ExactPairing X Y) :
    p.curryEvaluationIso.hom = MonoidalClosed.curry p.evaluation' := by
  apply MonoidalClosed.uncurry_injective
  rw [curryEvaluationIso, Iso.trans_hom]
  rw [MonoidalClosed.uncurry_natural_left]
  change
    Y ◁ (ρ_ X).inv ≫
        ((ihom.adjunction Y).homEquiv (X ⊗ 𝟙_ C) (𝟙_ C)).symm
          ((p.tensorLeftAdjunction.rightAdjointUniq
            (ihom.adjunction Y)).hom.app (𝟙_ C)) = _
  have huniq := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    p.tensorLeftAdjunction (ihom.adjunction Y) (𝟙_ C)
  change
    ((ihom.adjunction Y).homEquiv (X ⊗ 𝟙_ C) (𝟙_ C)).symm
        ((p.tensorLeftAdjunction.rightAdjointUniq
          (ihom.adjunction Y)).hom.app (𝟙_ C)) =
      p.tensorLeftAdjunction.counit.app (𝟙_ C) at huniq
  rw [huniq]
  rw [MonoidalClosed.uncurry_curry]
  rw [ExactPairing.tensorLeftAdjunction]
  rw [CategoryTheory.tensorLeftAdjunction]
  change
    Y ◁ (ρ_ X).inv ≫
      Y ◁ (𝟙 (X ⊗ 𝟙_ C)) ≫
      (α_ Y X (𝟙_ C)).inv ≫
      p.evaluation' ▷ (𝟙_ C) ≫ (λ_ (𝟙_ C)).hom = p.evaluation'
  monoidal

/-- Evaluation is recovered by uncurrying the forward comparison from a specified left dual to
the internal Hom into the tensor unit. -/
@[stacks 0FNZ "(3)"]
theorem uncurry_curryEvaluationIso_hom {X Y : C} [Closed Y]
    (p : ExactPairing X Y) :
    MonoidalClosed.uncurry p.curryEvaluationIso.hom = p.evaluation' := by
  rw [curryEvaluationIso_hom, MonoidalClosed.uncurry_curry]

/-- Currying the evaluation of an exact pairing always gives an isomorphism from the specified
left dual to the internal Hom into the tensor unit. -/
@[stacks 0FNZ "(2)", instance]
theorem isIso_curry_evaluation (X Y : C) [Closed Y]
    [ExactPairing X Y] :
    IsIso (MonoidalClosed.curry (ExactPairing.evaluation X Y)) := by
  change IsIso (MonoidalClosed.curry
    (inferInstance : ExactPairing X Y).evaluation')
  rw [← curryEvaluationIso_hom (inferInstance : ExactPairing X Y)]
  infer_instance

end ExactPairing

end

end CategoryTheory

