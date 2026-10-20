module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Bifunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# From coherent RHom comparisons to pointwise closed models

A coherent comparison of the canonical `RHom` bifunctor with a selected closed structure can be
combined with an explicit ambient tensor model.  The result is the pointwise
`RHom.ClosedComparison` used by fixed-source calculations.  Keeping this bridge in a separate leaf
makes the extra tensor-model input visible and avoids rebuilding the transported adjunction in
downstream developments.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [RHom.Has (A := A)]

/-- `0E1U:` A genuine parametrized tensor-`RHom` adjunction and an explicit ambient tensor model
determine the pointwise closed comparison used by fixed-source calculations. -/
@[stacks 0E1U "closed comparison from a parametrized RHom adjunction"]
noncomputable def ofAdjunction₂
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    RHom.ClosedComparison (A := A) where
  closed := H
  tensorModel := T
  adjunction := fun K =>
    (adj₂.adj K).ofNatIsoLeft (T.functorIsoTensorRight K).symm

/-- The selected closed structure of `ofAdjunction₂ H T adj₂` is `H`. -/
@[simp, stacks 0E1U "closed owner from a parametrized RHom adjunction"]
theorem ofAdjunction₂_closed
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    (ofAdjunction₂ H T adj₂).closed = H := rfl

/-- The ambient tensor model of `ofAdjunction₂ H T adj₂` is `T`. -/
@[simp, stacks 0E1U "tensor model from a parametrized RHom adjunction"]
theorem ofAdjunction₂_tensorModel
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (adj₂ : RHom.TensorAdjunction₂ (A := A)) :
    (ofAdjunction₂ H T adj₂).tensorModel = T := rfl

/-- The pointwise adjunction is obtained by transporting the parametrized adjunction along the
explicit ambient tensor model. -/
@[simp, stacks 0E1U "pointwise adjunction from a parametrized RHom adjunction"]
theorem ofAdjunction₂_adjunction
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (adj₂ : RHom.TensorAdjunction₂ (A := A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ofAdjunction₂ H T adj₂).adjunction K =
      (adj₂.adj K).ofNatIsoLeft (T.functorIsoTensorRight K).symm := rfl

section Braided

variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- The objectwise comparison from the pointwise view of a parametrized adjunction agrees with
the component of its coherent bifunctor comparison. -/
@[simp, stacks 0E1U "pointwise and coherent RHom comparisons agree"]
theorem ofAdjunction₂_objIso_eq_bifunctor
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (adj₂ : RHom.TensorAdjunction₂ (A := A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (ofAdjunction₂ H T adj₂).objIso K L =
      (RHom.BifunctorComparison.ofAdjunction H adj₂).objIso K L := sorry

end Braided

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [RHom.Has (A := A)]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]

/-- `0E1U:` A coherent canonical-`RHom` bifunctor comparison and an explicit ambient tensor model
determine the pointwise closed comparison used by fixed-source calculations. -/
@[stacks 0E1U "closed comparison from a coherent RHom bifunctor model"]
noncomputable def toClosedComparison
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A)) :
    RHom.ClosedComparison (A := A) where
  closed := M.closed
  tensorModel := T
  adjunction := fun K =>
    (DerivedTensor.Right.Closed.adjunctionOf M.closed T K).ofNatIsoRight
      (M.targetIso K).symm

/-- The selected closed owner of `M.toClosedComparison T` is the one carried by `M`. -/
@[simp, stacks 0E1U "closed owner of the coherent RHom model"]
theorem toClosedComparison_closed
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A)) :
    (M.toClosedComparison T).closed = M.closed := rfl

/-- The tensor model of `M.toClosedComparison T` is the explicit input `T`. -/
@[simp, stacks 0E1U "tensor model of the coherent RHom model"]
theorem toClosedComparison_tensorModel
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A)) :
    (M.toClosedComparison T).tensorModel = T := rfl

/-- The canonical-`RHom` adjunction stored in `M.toClosedComparison T` is the selected closed
adjunction transported along the inverse coherent fixed-source comparison. -/
@[simp, stacks 0E1U "adjunction of the coherent RHom model"]
theorem toClosedComparison_adjunction
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.toClosedComparison T).adjunction K =
      (DerivedTensor.Right.Closed.adjunctionOf M.closed T K).ofNatIsoRight
        (M.targetIso K).symm := rfl

/-- Reconstructing the fixed-source comparison through `M.toClosedComparison T` recovers the
coherent comparison carried by `M`. -/
@[simp, stacks 0E1U "fixed-source iso of the coherent RHom model"]
theorem toClosedComparison_targetIso
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (M.toClosedComparison T).targetIso K = M.targetIso K := by
  apply Iso.ext
  ext L
  apply ((DerivedTensor.Right.Closed.adjunctionOf M.closed T K).homEquiv _ _).symm.injective
  change
    ((DerivedTensor.Right.Closed.adjunctionOf M.closed T K).homEquiv _ _).symm
        ((((DerivedTensor.Right.Closed.adjunctionOf M.closed T K).ofNatIsoRight
          (M.targetIso K).symm).rightAdjointUniq
            (DerivedTensor.Right.Closed.adjunctionOf M.closed T K)).hom.app L) =
      ((DerivedTensor.Right.Closed.adjunctionOf M.closed T K).homEquiv _ _).symm
        ((M.targetIso K).hom.app L)
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  rfl

/-- Objectwise, conversion to a pointwise closed comparison preserves the coherent comparison
isomorphism. -/
@[simp, stacks 0E1U "object iso of the coherent RHom model"]
theorem toClosedComparison_objIso
    (M : RHom.BifunctorComparison (A := A))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u} A))
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (M.toClosedComparison T).objIso K L = M.objIso K L := by
  change ((M.toClosedComparison T).targetIso K).app L = (M.targetIso K).app L
  rw [toClosedComparison_targetIso]
  rfl

end CategoryTheory.DerivedCategory.InternalHom.RHom.BifunctorComparison
