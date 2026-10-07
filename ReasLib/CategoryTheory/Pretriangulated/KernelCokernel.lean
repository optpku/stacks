module

public import ReasLib.CategoryTheory.Arrow.ProjectionCoprojection
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel-Cokernel Normal Forms in Pretriangulated Categories

The generic arrow-category normal form lives in
`CategoryTheory.Arrow.IsProjectionThenCoprojection`. This leaf proves that in a
pretriangulated category it is equivalent to the existence of either a kernel
or a cokernel.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 05QU: a morphism with a kernel has biproduct
projection-coprojection normal form in the arrow category. -/
@[stacks 05QU]
theorem isProjectionThenCoprojection_of_hasKernel {X Y : D} (f : X ⟶ Y)
    (hf : HasKernel f) : Arrow.IsProjectionThenCoprojection (Arrow.mk f) := sorry

/-- Stacks 05QU: a morphism with a cokernel has biproduct
projection-coprojection normal form in the arrow category. -/
@[stacks 05QU]
theorem isProjectionThenCoprojection_of_hasCokernel {X Y : D} (f : X ⟶ Y)
    (hf : HasCokernel f) : Arrow.IsProjectionThenCoprojection (Arrow.mk f) := sorry

/-- Stacks 05QU: in a pretriangulated category, a morphism has a kernel if and
only if it has a cokernel. -/
@[stacks 05QU]
theorem hasKernel_iff_hasCokernel {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔ HasCokernel f := sorry

/-- Stacks 05QU: in a pretriangulated category, a morphism has a kernel if and
only if its arrow is isomorphic to a biproduct projection followed by a
coprojection. -/
@[stacks 05QU]
theorem hasKernel_iff_isProjectionThenCoprojection {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔ Arrow.IsProjectionThenCoprojection (Arrow.mk f) := sorry

/-- Stacks 05QU: in a pretriangulated category, a morphism has a cokernel if
and only if its arrow is isomorphic to a biproduct projection followed by a
coprojection. -/
@[stacks 05QU]
theorem hasCokernel_iff_isProjectionThenCoprojection {X Y : D} (f : X ⟶ Y) :
    HasCokernel f ↔ Arrow.IsProjectionThenCoprojection (Arrow.mk f) := sorry

end CategoryTheory.Pretriangulated
