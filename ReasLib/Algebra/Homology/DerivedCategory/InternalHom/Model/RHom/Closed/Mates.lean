/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed.Currying
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mate specifications carried by a closed comparison

This leaf names the concrete transposes of internal-Hom composition and the tensor-left/right
comparisons at an `RHom.ClosedComparison`.  Each public comparison is tied to its transpose by the
same selected adjunction; no alternate map or local instance is introduced.

@stack 0A8J
@stack 0BYN
@stack 0A67
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]

local notation "D(" A ")" => DerivedCategory (ModuleCat A)

/-- The selected-adjunction transpose of bundled internal-Hom composition. -/
@[stacks 0A8J "bundled internal-Hom composition transpose"]
noncomputable def derivedInternalHomCompTranspose
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj
        (DerivedTensor.Right.obj
          ((MonoidalClosed.ihomOf P.closed L).obj M)
          ((MonoidalClosed.ihomOf P.closed K).obj L)) K ⟶ M :=
  (CategoryTheory.derivedTensorProduct_comm
      (DerivedTensor.Right.obj
        ((MonoidalClosed.ihomOf P.closed L).obj M)
        ((MonoidalClosed.ihomOf P.closed K).obj L)) K).hom ≫
    (P.derivedTensorProductMap (P.derivedInternalHomComp K L M)).app K ≫
    (CategoryTheory.derivedTensorProduct_comm
      K ((MonoidalClosed.ihomOf P.closed K).obj M)).hom ≫
    P.counitOf K M

/-- Bundled internal-Hom composition is the mate of its named transpose. -/
@[stacks 0A8J "bundled internal-Hom composition mate specification"]
theorem derivedInternalHomComp_eq_homEquiv
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.derivedInternalHomComp K L M =
      (P.selectedAdjunction K).homEquiv _ _
        (P.derivedInternalHomCompTranspose K L M) := sorry

/-- Inverse selected adjunction recovers the named composition transpose. -/
@[stacks 0A8J "bundled internal-Hom composition inverse mate"]
theorem derivedInternalHomComp_homEquiv_symm
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    ((P.selectedAdjunction K).homEquiv _ _).symm
        (P.derivedInternalHomComp K L M) =
      P.derivedInternalHomCompTranspose K L M := by
  rw [P.derivedInternalHomComp_eq_homEquiv K L M]
  exact Equiv.symm_apply_apply _ _

/-- The associativity-evaluation transpose of the bundled tensor-left comparison. -/
@[stacks 0BYN "bundled tensor-left comparison transpose"]
noncomputable def tensorLeftComparisonTranspose
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj
        (DerivedTensor.Right.obj K ((MonoidalClosed.ihomOf P.closed M).obj L)) M ⟶
      DerivedTensor.Right.obj K L :=
  (P.derivedTensorProductAssociator K
      ((MonoidalClosed.ihomOf P.closed M).obj L) M).hom ≫
    (P.derivedTensorProductMap (P.counitOf M L)).app K

/-- The bundled tensor-left comparison is the mate of its named transpose. -/
@[stacks 0BYN "bundled tensor-left comparison mate specification"]
theorem tensorLeftComparison_eq_homEquiv
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.tensorLeftComparison K L M =
      (P.selectedAdjunction M).homEquiv _ _
        (P.tensorLeftComparisonTranspose K L M) := sorry

/-- Inverse selected adjunction recovers the named tensor-left transpose. -/
@[stacks 0BYN "bundled tensor-left comparison inverse mate"]
theorem tensorLeftComparison_homEquiv_symm
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    ((P.selectedAdjunction M).homEquiv _ _).symm
        (P.tensorLeftComparison K L M) =
      P.tensorLeftComparisonTranspose K L M := by
  rw [P.tensorLeftComparison_eq_homEquiv K L M]
  exact Equiv.symm_apply_apply _ _

/-- The reassociation, symmetry, composition, and evaluation transpose of the tensor-right map. -/
@[stacks 0A67 "bundled tensor-right comparison transpose"]
noncomputable def tensorRightComparisonTranspose
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    DerivedTensor.Right.obj
        (DerivedTensor.Right.obj ((MonoidalClosed.ihomOf P.closed L).obj M) K)
        ((MonoidalClosed.ihomOf P.closed K).obj L) ⟶ M :=
  (P.derivedTensorProductAssociator
      ((MonoidalClosed.ihomOf P.closed L).obj M) K
      ((MonoidalClosed.ihomOf P.closed K).obj L)).hom ≫
    (P.derivedTensorProductMap
      (CategoryTheory.derivedTensorProduct_comm K
        ((MonoidalClosed.ihomOf P.closed K).obj L)).hom).app
          ((MonoidalClosed.ihomOf P.closed L).obj M) ≫
    (P.derivedTensorProductAssociator
      ((MonoidalClosed.ihomOf P.closed L).obj M)
      ((MonoidalClosed.ihomOf P.closed K).obj L) K).inv ≫
    (DerivedTensor.Right.functor K).map (P.derivedInternalHomComp K L M) ≫
    P.counitOf K M

/-- The bundled tensor-right comparison is the mate of its named transpose. -/
@[stacks 0A67 "bundled tensor-right comparison mate specification"]
theorem tensorRightComparison_eq_homEquiv
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    P.tensorRightComparison K L M =
      (P.selectedAdjunction ((MonoidalClosed.ihomOf P.closed K).obj L)).homEquiv _ _
        (P.tensorRightComparisonTranspose K L M) := sorry

/-- Inverse selected adjunction recovers the named tensor-right transpose. -/
@[stacks 0A67 "bundled tensor-right comparison inverse mate"]
theorem tensorRightComparison_homEquiv_symm
    (P : RHom.ClosedComparison (A := A)) (K L M : D(A)) :
    ((P.selectedAdjunction
      ((MonoidalClosed.ihomOf P.closed K).obj L)).homEquiv _ _).symm
        (P.tensorRightComparison K L M) =
      P.tensorRightComparisonTranspose K L M := by
  rw [P.tensorRightComparison_eq_homEquiv K L M]
  exact Equiv.symm_apply_apply _ _

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison
