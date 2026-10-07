module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Associativity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-tensor associativity carried by a closed comparison

This leaf specializes the model-parametrized associativity owner
`DerivedTensor.Right.tensorAssoc` to an `RHom.ClosedComparison`.  It does not choose a monoidal
structure or a derived-tensor model.

@stack 0BYJ
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]

local notation "D(" A ")" => DerivedCategory (ModuleCat A)

section Monoidal

variable [MonoidalCategory D(A)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]

/-- Ambient right tensoring compared with canonical fixed-right derived tensoring through `P`. -/
@[stacks 064M "bundled ambient-right derived tensor comparison"]
noncomputable abbrev tensoringRightIsoDerivedTensorProduct
    (P : RHom.ClosedComparison (A := A)) (L : D(A)) :
    MonoidalCategory.tensorRight L ≅ DerivedTensor.Right.functor L :=
  P.tensorModel.tensorRightIsoFunctor L

/-- Objectwise ambient/fixed-right tensor comparison carried by `P`. -/
@[stacks 064M "bundled ambient derived tensor object comparison"]
noncomputable abbrev tensorObjIsoDerivedTensorProduct
    (P : RHom.ClosedComparison (A := A)) (K L : D(A)) :
    K ⊗ L ≅ DerivedTensor.Right.obj K L :=
  P.tensorModel.tensorIsoObj K L

/-- Successive fixed-right derived tensor functors compared with tensoring by their product. -/
@[stacks 0BYJ "bundled derived tensor associativity"]
noncomputable abbrev derivedTensorProductTensorIso
    (P : RHom.ClosedComparison (A := A)) (L M : D(A)) :
    DerivedTensor.Right.functor L ⋙ DerivedTensor.Right.functor M ≅
      DerivedTensor.Right.functor (DerivedTensor.Right.obj L M) :=
  DerivedTensor.Right.tensorAssoc P.tensorModel L M

/-- Objectwise derived-tensor associator carried by `P`. -/
@[stacks 0BYJ "bundled derived tensor associator"]
noncomputable abbrev derivedTensorProductAssociator
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj (DerivedTensor.Right.obj K L) M ≅
      DerivedTensor.Right.obj K (DerivedTensor.Right.obj L M) :=
  DerivedTensor.Right.assoc P.tensorModel K L M

/-- The bundled tensor-functor comparison evaluates to the bundled objectwise associator. -/
@[simp]
theorem derivedTensorProductTensorIso_app
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    (P.derivedTensorProductTensorIso L M).app K =
      P.derivedTensorProductAssociator K L M := rfl

/-- Naturality of the bundled derived-tensor associator in the left variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_hom_naturality_left
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ : D(A)} (f : K₁ ⟶ K₂) (L M : D(A)) :
    (DerivedTensor.Right.functor M).map
          ((DerivedTensor.Right.functor L).map f) ≫
      (P.derivedTensorProductAssociator K₂ L M).hom =
      (P.derivedTensorProductAssociator K₁ L M).hom ≫
        (DerivedTensor.Right.functor (DerivedTensor.Right.obj L M)).map f :=
  DerivedTensor.Right.assoc_hom_naturality P.tensorModel f L M

/-- Naturality of the inverse bundled derived-tensor associator in the left variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_inv_naturality_left
    (P : RHom.ClosedComparison (A := A))
    {K₁ K₂ : D(A)} (f : K₁ ⟶ K₂) (L M : D(A)) :
    (DerivedTensor.Right.functor (DerivedTensor.Right.obj L M)).map f ≫
        (P.derivedTensorProductAssociator K₂ L M).inv =
      (P.derivedTensorProductAssociator K₁ L M).inv ≫
        (DerivedTensor.Right.functor M).map
          ((DerivedTensor.Right.functor L).map f) :=
  DerivedTensor.Right.assoc_inv_naturality P.tensorModel f L M

end Monoidal

section Braided

variable [MonoidalCategory D(A)] [BraidedCategory D(A)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]

/-- Naturality of the bundled derived-tensor associator in the middle variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_hom_naturality_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) (M : D(A)) :
    (DerivedTensor.Right.functor M).map ((P.derivedTensorProductMap f).app K) ≫
        (P.derivedTensorProductAssociator K L₂ M).hom =
      (P.derivedTensorProductAssociator K L₁ M).hom ≫
        (P.derivedTensorProductMap ((DerivedTensor.Right.functor M).map f)).app K :=
  DerivedTensor.Right.assoc_hom_naturality_middle
    P.closed P.tensorModel K f M

/-- Naturality of the inverse bundled derived-tensor associator in the middle variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_inv_naturality_middle
    (P : RHom.ClosedComparison (A := A))
    (K : D(A)) {L₁ L₂ : D(A)} (f : L₁ ⟶ L₂) (M : D(A)) :
    (P.derivedTensorProductMap ((DerivedTensor.Right.functor M).map f)).app K ≫
        (P.derivedTensorProductAssociator K L₂ M).inv =
      (P.derivedTensorProductAssociator K L₁ M).inv ≫
        (DerivedTensor.Right.functor M).map ((P.derivedTensorProductMap f).app K) :=
  DerivedTensor.Right.assoc_inv_naturality_middle
    P.closed P.tensorModel K f M

/-- Naturality of the bundled derived-tensor associator in the right variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_hom_naturality_right
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (P.derivedTensorProductMap f).app (DerivedTensor.Right.obj K L) ≫
        (P.derivedTensorProductAssociator K L M₂).hom =
      (P.derivedTensorProductAssociator K L M₁).hom ≫
        (P.derivedTensorProductMap ((P.derivedTensorProductMap f).app L)).app K :=
  DerivedTensor.Right.assoc_hom_naturality_right
    P.closed P.tensorModel K L f

/-- Naturality of the inverse bundled derived-tensor associator in the right variable. -/
@[reassoc]
theorem derivedTensorProductAssociator_inv_naturality_right
    (P : RHom.ClosedComparison (A := A))
    (K L : D(A)) {M₁ M₂ : D(A)} (f : M₁ ⟶ M₂) :
    (P.derivedTensorProductMap ((P.derivedTensorProductMap f).app L)).app K ≫
        (P.derivedTensorProductAssociator K L M₂).inv =
      (P.derivedTensorProductAssociator K L M₁).inv ≫
        (P.derivedTensorProductMap f).app (DerivedTensor.Right.obj K L) :=
  DerivedTensor.Right.assoc_inv_naturality_right
    P.closed P.tensorModel K L f

end Braided

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison
