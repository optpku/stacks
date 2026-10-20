/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Shift.CommShiftTwo
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated internal Hom

For the target variable, internal Hom is the right adjoint of tensoring with its fixed source.
For the contravariant source variable, tensoring with every testing object is needed instead.
The tensor bifunctor's coherent shifts determine the source shift isomorphisms, including the
quadratic sign required to turn the two-variable sign rule into ordinary shift coherence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A fixed left tensor factor supplies the shift compatibility of its internal-Hom right adjoint.
The hypothesis is deliberately factor-local, so a category may support exactness only for a
specified class of tensor factors. -/
@[stacks 08JC "internal-Hom target-variable shift owner"]
noncomputable instance ihom_commShift_of_tensorLeft (K : C)
    [hK : (tensorLeft K).CommShift ℤ] :
    (ihom K).CommShift ℤ :=
  (ihom.adjunction K).rightAdjointCommShift ℤ

/-- A triangulated fixed left tensor functor makes its internal-Hom right adjoint triangulated. -/
@[stacks 08JC "internal-Hom target-variable triangulated owner",
  stacks 08I0 "internal-Hom preserves triangles in the target variable"]
noncomputable instance ihom_isTriangulated_of_tensorLeft (K : C)
    [hK : (tensorLeft K).CommShift ℤ] [hTri : (tensorLeft K).IsTriangulated] :
    (ihom K).IsTriangulated := sorry

/-- Moving the first tensor factor through a shift, naturally in the testing object. -/
noncomputable def tensorLeftShiftFirstIso
    [hTensor : (curriedTensor C).CommShift₂Int] (K : C) (n : ℤ) :
    tensorLeft (K⟦n⟧) ≅ tensorLeft K ⋙ shiftFunctor C n :=
  NatIso.ofComponents (fun W ↦ ((tensorRight W).commShiftIso n).app K)
    (by intro W W' f; sorry)

/-- The source shift comparison is obtained from actual tensor shift maps by uniqueness of
right adjoints. The sign `(-1)^(n(n-1)/2)` corrects the mixed tensor-shift sign cocycle. -/
noncomputable def internalHomShiftSourceIso
    [hTensor : (curriedTensor C).CommShift₂Int] (K L : C) (n : ℤ) :
    (ihom (K⟦-n⟧)).obj L ≅ ((ihom K).obj L)⟦n⟧ :=
  let adj := ((ihom.adjunction K).comp
    (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction).ofNatIsoLeft
      (tensorLeftShiftFirstIso K (-n)).symm
  ((-1 : (CatCenter C)ˣ) ^ (n * (n - 1) / 2)) •
    (((ihom.adjunction (K⟦-n⟧)).rightAdjointUniq adj).app L ≪≫
      ((ihom K).commShiftIso n).app L)

/-- The contravariant source comparison uses the opposite category's negative shift. -/
noncomputable def internalHomFlipShiftIso
    [hTensor : (curriedTensor C).CommShift₂Int] (L : C) (n : ℤ) :
    shiftFunctor Cᵒᵖ n ⋙ (internalHom (C := C)).flip.obj L ≅
      (internalHom (C := C)).flip.obj L ⋙ shiftFunctor C n :=
  Functor.isoWhiskerRight (Pretriangulated.shiftFunctorOpIso C n (-n) (add_neg_cancel n))
      ((internalHom (C := C)).flip.obj L) ≪≫
    NatIso.ofComponents (fun K ↦ internalHomShiftSourceIso K.unop L n)
      (by intro K K' f; sorry)

/-- Coherent shifts of the tensor bifunctor supply source-variable internal-Hom shifts.
A condition on tensoring with the single output object `L` would not suffice. -/
@[stacks 08JC "internal-Hom source-variable shift owner"]
noncomputable instance internalHomFlip_commShift_of_tensorRight (L : C)
    [hTensor : (curriedTensor C).CommShift₂Int] :
    ((internalHom (C := C)).flip.obj L).CommShift ℤ where
  commShiftIso := internalHomFlipShiftIso L
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- Exact tensoring with every testing object makes the source-variable internal-Hom functor
triangulated, with the source shift comparison induced by the coherent tensor bifunctor. -/
@[stacks 08JC "internal-Hom source-variable triangulated owner",
  stacks 08I0 "internal-Hom preserves triangles in the source variable"]
noncomputable instance internalHomFlip_isTriangulated_of_tensorRight (L : C)
    [hTensor : (curriedTensor C).CommShift₂Int]
    [hTri : ∀ W : C, (tensorRight W).IsTriangulated] :
    ((internalHom (C := C)).flip.obj L).IsTriangulated := sorry

end CategoryTheory.MonoidalClosed
