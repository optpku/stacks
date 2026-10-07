module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.BraidedClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated internal Hom

This leaf records the exactness boundary for a closed monoidal triangulated category.  A fixed
tensor factor is the primitive input; the corresponding internal-Hom functor is the right adjoint
and therefore inherits the shift and triangulated interfaces.  The source-variable form uses the
right-tensor presentation supplied by the braided closed bridge.
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
    (ihom K).CommShift ℤ := sorry

/-- A triangulated fixed left tensor functor makes its internal-Hom right adjoint triangulated. -/
@[stacks 08JC "internal-Hom target-variable triangulated owner",
  stacks 08I0 "internal-Hom preserves triangles in the target variable"]
noncomputable instance ihom_isTriangulated_of_tensorLeft (K : C)
    [hK : (tensorLeft K).CommShift ℤ] [hTri : (tensorLeft K).IsTriangulated] :
    (ihom K).IsTriangulated := sorry

/-- A fixed right tensor factor supplies the shift compatibility of the source-variable internal
Hom functor.  The right-tensor functor is written as the canonical `tensoringRight` object so the
assumption is independent of any chosen notation. -/
@[stacks 08JC "internal-Hom source-variable shift owner"]
noncomputable instance internalHomFlip_commShift_of_tensorRight (L : C)
    [BraidedCategory C] [hL : ((tensoringRight C).obj L).CommShift ℤ] :
    ((internalHom (C := C)).flip.obj L).CommShift ℤ := sorry

/-- A triangulated fixed right tensor functor makes its source-variable internal-Hom functor
triangulated. -/
@[stacks 08JC "internal-Hom source-variable triangulated owner",
  stacks 08I0 "internal-Hom preserves triangles in the source variable"]
noncomputable instance internalHomFlip_isTriangulated_of_tensorRight (L : C)
    [BraidedCategory C] [hL : ((tensoringRight C).obj L).CommShift ℤ]
    [hTri : ((tensoringRight C).obj L).IsTriangulated] :
    ((internalHom (C := C)).flip.obj L).IsTriangulated := sorry

end CategoryTheory.MonoidalClosed
