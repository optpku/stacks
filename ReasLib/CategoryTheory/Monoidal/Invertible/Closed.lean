/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor inverses and internal-Hom duals

In a braided monoidal category, a right tensor inverse of a closed object is its internal-Hom
dual. This is the categorical owner of the corresponding statements for module sheaves.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace MonoidalClosed

namespace RightInverse

/-- A specified right tensor inverse in a braided monoidal category determines exact-pairing
data.  The reverse tensor comparison is supplied by the braiding, and
`ExactPairing.ofTensorInverse` normalizes the resulting evaluation so that both triangle
identities hold. -/
@[stacks 0B8K "tensor inverse pairing", stacks 0B8N "tensor inverse pairing",
  implicit_reducible]
def pairing [BraidedCategory C]
    (X Y : C) (e : X ⊗ Y ≅ 𝟙_ C) : ExactPairing X Y :=
  ExactPairing.ofTensorInverse e (β_ Y X ≪≫ e)

/-- The coevaluation of the exact pairing associated to a right tensor inverse is the inverse
of the supplied tensor comparison. -/
@[simp]
theorem pairing_coevaluation [BraidedCategory C]
    (X Y : C) (e : X ⊗ Y ≅ 𝟙_ C) :
    (pairing X Y e).coevaluation' = e.inv :=
  ExactPairing.ofTensorInverse.coevaluation e (β_ Y X ≪≫ e)

/-- The evaluation of the exact pairing associated to a right tensor inverse is the normalized
evaluation obtained from the supplied comparison and the braiding. -/
@[simp]
theorem pairing_evaluation [BraidedCategory C]
    (X Y : C) (e : X ⊗ Y ≅ 𝟙_ C) :
    (pairing X Y e).evaluation' =
      ExactPairing.TensorInverse.evaluation e (β_ Y X ≪≫ e) :=
  ExactPairing.ofTensorInverse.evaluation e (β_ Y X ≪≫ e)

/-- A specified right tensor inverse of a closed object is canonically isomorphic to its
internal-Hom dual.  The isomorphism is the closed comparison attached to the braided swap of
the explicit tensor-inverse pairing; no representative or inverse is chosen from a proposition. -/
@[stacks 0B8K "tensor inverse is dual", stacks 0B8N "consequence (3)"]
noncomputable def isoIhomUnit [BraidedCategory C]
    (X Y : C) [Closed X] (e : X ⊗ Y ≅ 𝟙_ C) :
    Y ≅ (ihom X).obj (𝟙_ C) :=
  (ExactPairing.braidedSwap (pairing X Y e)).curryEvaluationIso

/-- The forward map of `isoIhomUnit` is the curried evaluation of the swapped
tensor-inverse pairing. -/
theorem isoIhomUnit_hom [BraidedCategory C]
    (X Y : C) [Closed X] (e : X ⊗ Y ≅ 𝟙_ C) :
    (isoIhomUnit X Y e).hom =
      curry (ExactPairing.braidedSwap (pairing X Y e)).evaluation' :=
  ExactPairing.curryEvaluationIso_hom _

/-- The inverse of `isoIhomUnit`, followed by the curried tensor-inverse evaluation, is the
identity. -/
theorem isoIhomUnit_inv_comp_curry [BraidedCategory C]
    (X Y : C) [Closed X] (e : X ⊗ Y ≅ 𝟙_ C) :
    (isoIhomUnit X Y e).inv ≫
        curry (ExactPairing.braidedSwap (pairing X Y e)).evaluation' =
      𝟙 ((ihom X).obj (𝟙_ C)) := by
  rw [← isoIhomUnit_hom, Iso.inv_hom_id]

/-- Uncurrying the forward map of `isoIhomUnit` recovers the evaluation of the
swapped tensor-inverse pairing. -/
theorem uncurry_isoIhomUnit_hom [BraidedCategory C]
    (X Y : C) [Closed X] (e : X ⊗ Y ≅ 𝟙_ C) :
    uncurry (isoIhomUnit X Y e).hom =
      (ExactPairing.braidedSwap (pairing X Y e)).evaluation' :=
  ExactPairing.uncurry_curryEvaluationIso_hom _

end RightInverse

end MonoidalClosed

namespace MonoidalCategory.isInvertibleObject

/-- Every invertible object is closed: a quasi-inverse to left tensoring is its canonical right
adjoint. The low priority lets a purpose-built `MonoidalClosed` structure retain definitional
control of internal Hom. -/
@[stacks 0FFN "invertible objects are closed"]
noncomputable instance (priority := 90) closed
    (X : C) [isInvertibleObject X] : Closed X where
  rightAdj := (tensorLeft X).asEquivalence.inverse
  adj := (tensorLeft X).asEquivalence.toAdjunction

/-- The inverse of tensoring on the right by an invertible object is canonically its
internal-Hom functor. -/
@[stacks 01CU "tensor inverse as internal Hom"]
noncomputable def inverseIsoIhom [BraidedCategory C]
    (X : C) [Closed X] [isInvertibleObject X] :
    (tensorRight X).asEquivalence.inverse ≅ ihom X :=
  Adjunction.rightAdjointUniq
    (tensorRight X).asEquivalence.toAdjunction
    ((ihom.adjunction X).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight X))

/-- The internal-Hom dual of an invertible object is invertible. The `Closed X` input keeps the
instance head definitionally aligned with the caller's chosen internal-Hom structure. This named
instance is also the explicit theorem-level API for the fact. -/
@[stacks 040A "(2), categorical dual", stacks 01CT "(2), categorical dual"]
instance ihomUnit [BraidedCategory C]
    (X : C) [Closed X] [isInvertibleObject X] :
    isInvertibleObject ((ihom X).obj (𝟙_ C)) :=
  isInvertibleObject.of_iso
    (MonoidalClosed.RightInverse.isoIhomUnit X (inverse X) (tensorInverseIso X))
    (inferInstance : isInvertibleObject (inverse X))

/-- Evaluation into the tensor unit is an isomorphism for an invertible object. The `Closed X`
input preserves the caller's chosen evaluation morphism. This named instance is also the explicit
theorem-level API for the fact. -/
@[stacks 040A "(2), categorical evaluation", stacks 01CT "(2), categorical evaluation"]
instance evaluationIsIso [BraidedCategory C]
    (X : C) [Closed X] [isInvertibleObject X] :
    IsIso ((ihom.ev X).app (𝟙_ C)) := by
  let e : X ⊗ inverse X ≅ 𝟙_ C := tensorInverseIso X
  let p : ExactPairing X (inverse X) :=
    MonoidalClosed.RightInverse.pairing X (inverse X) e
  let q : ExactPairing (inverse X) X := p.braidedSwap
  let i : inverse X ≅ (ihom X).obj (𝟙_ C) :=
    MonoidalClosed.RightInverse.isoIhomUnit X (inverse X) e
  -- Local instance justification (proof-local temporary data): the explicit pairing evaluation is transported through the chosen inverse equivalence.
  haveI hp : IsIso p.evaluation' := by
    rw [show p.evaluation' =
      ExactPairing.TensorInverse.evaluation e (β_ (inverse X) X ≪≫ e) from
        MonoidalClosed.RightInverse.pairing_evaluation X (inverse X) e]
    dsimp [ExactPairing.TensorInverse.evaluation]
    infer_instance
  -- Local instance justification (proof-local temporary data): the swapped pairing evaluation is the second transported evaluation map used below.
  haveI hq : IsIso q.evaluation' := by
    change IsIso ((β_ X (inverse X)).hom ≫ p.evaluation')
    infer_instance
  have hcomp : X ◁ i.hom ≫ (ihom.ev X).app (𝟙_ C) = q.evaluation' := by
    rw [← MonoidalClosed.uncurry_eq]
    exact MonoidalClosed.RightInverse.uncurry_isoIhomUnit_hom X (inverse X) e
  -- Local instance justification (proof-local temporary data): the displayed composite is identified with `q.evaluation'` and is used by the final cancellation step.
  haveI : IsIso (X ◁ i.hom ≫ (ihom.ev X).app (𝟙_ C)) := by
    rw [hcomp]
    exact hq
  exact IsIso.of_isIso_comp_left
    (X ◁ i.hom) ((ihom.ev X).app (𝟙_ C))



end MonoidalCategory.isInvertibleObject

end CategoryTheory
