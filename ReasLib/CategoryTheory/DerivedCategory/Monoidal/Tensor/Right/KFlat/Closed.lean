/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Closed
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed fixed-right derived tensoring from K-flat resolutions

A selected functorial K-flat resolution supplies the explicit ambient model needed to transport
the braided closed adjunction to canonical fixed-right derived tensoring.  No monoidality claim is
made for the ambient homotopy localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.DerivedTensor.Right.KFlat.Closed

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [HomotopyCategory.KFlat.TensorDescends (C := C)]
variable [DerivedCategory.KFlat.IsLocalization (C := C)]

namespace Parametrized

/-- Stacks 0FPB: the K-flat fixed-right adjunction selected by explicit resolution and bundled
right internal-Hom owners. -/
@[stacks 0FPB "K-flat fixed-right adjunction from parametrized owners"]
noncomputable abbrev adjunction
    (H : RightInternalHom (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ⊣ H.hom.obj (Opposite.op E) :=
  DerivedTensor.Right.Closed.Parametrized.adjunction H (KFlat.modelFamily P) E

/-- Stacks 0FPB: the K-flat fixed-right Hom equivalence selected by explicit resolution and
bundled right internal-Hom owners. -/
@[stacks 0FPB "K-flat fixed-right Hom equivalence from parametrized owners"]
noncomputable abbrev homEquiv
    (H : RightInternalHom (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    ((DerivedTensor.Right.functor E).obj K ⟶ N) ≃
      (K ⟶ (H.hom.obj (Opposite.op E)).obj N) :=
  (adjunction H P E).homEquiv K N

/-- Stacks 0FPB: the inverse K-flat fixed-right Hom equivalence selected by explicit resolution
and bundled right internal-Hom owners. -/
@[stacks 0FPB "K-flat fixed-right uncurrying equivalence from parametrized owners"]
noncomputable abbrev uncurryEquiv
    (H : RightInternalHom (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    (K ⟶ (H.hom.obj (Opposite.op E)).obj N) ≃
      ((DerivedTensor.Right.functor E).obj K ⟶ N) :=
  (homEquiv H P E K N).symm

end Parametrized

/-- Stacks 0FPB: the K-flat fixed-right adjunction selected by explicit resolution and closed
owners.  Downstream code can use this entry without installing a local closed instance. -/
@[stacks 0FPB "K-flat fixed-right adjunction from explicit owners"]
noncomputable abbrev adjunctionOf
    (H : MonoidalClosed (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ⊣ MonoidalClosed.ihomOf H E :=
  Parametrized.adjunction (RightInternalHom.ofBraidedClosedOf H) P E

/-- Stacks 0FPB: the K-flat fixed-right Hom equivalence selected by explicit resolution and
closed owners. -/
@[stacks 0FPB "K-flat fixed-right Hom equivalence from explicit owners"]
noncomputable abbrev homEquivOf
    (H : MonoidalClosed (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    ((DerivedTensor.Right.functor E).obj K ⟶ N) ≃
      (K ⟶ (MonoidalClosed.ihomOf H E).obj N) :=
  Parametrized.homEquiv (RightInternalHom.ofBraidedClosedOf H) P E K N

/-- Stacks 0FPB: the inverse K-flat fixed-right Hom equivalence selected by explicit resolution
and closed owners. -/
@[stacks 0FPB "K-flat fixed-right uncurrying equivalence from explicit owners"]
noncomputable abbrev uncurryEquivOf
    (H : MonoidalClosed (DerivedCategory C))
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    (K ⟶ (MonoidalClosed.ihomOf H E).obj N) ≃
      ((DerivedTensor.Right.functor E).obj K ⟶ N) :=
  (homEquivOf H P E K N).symm

variable [MonoidalClosed (DerivedCategory C)]

/-- Stacks 0FPB: the fixed-right derived tensor/internal-Hom adjunction obtained from a selected
functorial K-flat resolution. -/
@[stacks 0FPB "K-flat fixed-right closed adjunction"]
noncomputable abbrev adjunction
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    DerivedTensor.Right.functor E ⊣ (ihom E) :=
  adjunctionOf (inferInstance : MonoidalClosed (DerivedCategory C)) P E

/-- Stacks 0FPB: the source-facing Hom equivalence furnished by a selected K-flat resolution. -/
@[stacks 0FPB "K-flat fixed-right closed Hom equivalence"]
noncomputable abbrev homEquiv
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    ((DerivedTensor.Right.functor E).obj K ⟶ N) ≃ (K ⟶ (ihom E).obj N) :=
  (adjunction P E).homEquiv K N

/-- Stacks 0FPB: the source-facing inverse Hom equivalence furnished by a selected K-flat
resolution. -/
@[stacks 0FPB "K-flat fixed-right closed uncurrying equivalence"]
noncomputable abbrev uncurryEquiv
    (P : HomotopyCategory.KFlat.ResolutionFunctor C) (E K N : DerivedCategory C)
    [DerivedTensor.Right.Has (C := C)] :
    (K ⟶ (ihom E).obj N) ≃ ((DerivedTensor.Right.functor E).obj K ⟶ N) :=
  (homEquiv P E K N).symm

end CategoryTheory.DerivedCategory.DerivedTensor.Right.KFlat.Closed
