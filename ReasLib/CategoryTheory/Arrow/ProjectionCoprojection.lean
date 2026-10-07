module

public import ReasLib.CategoryTheory.Arrow.KernelCokernel
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Biproduct Projection-Coprojection Arrows

This leaf supplies the canonical arrow `K ⊞ Z ⟶ Z ⊞ Q` obtained by a
biproduct projection followed by a biproduct coprojection, together with the
isomorphism-invariant predicate for this normal form.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.Arrow

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- Stacks 05QU: the canonical arrow from `K ⊞ Z` to `Z ⊞ Q` given by the
projection onto `Z` followed by the coprojection from `Z`. -/
@[stacks 05QU]
def projectionThenCoprojection (K Z Q : C) : Arrow C :=
  Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)

/-- Stacks 05QU: an arrow is in biproduct projection-coprojection normal form
when it is isomorphic in `Arrow C` to `projectionThenCoprojection K Z Q` for
some `K`, `Z`, and `Q`. -/
@[stacks 05QU]
def IsProjectionThenCoprojection (f : Arrow C) : Prop :=
  ∃ K Z Q : C, IsIsomorphic f (projectionThenCoprojection K Z Q)

/-- Stacks 05QU: the canonical projection-coprojection arrow has a kernel. -/
@[stacks 05QU]
instance (priority := 100) hasKernel_projectionThenCoprojection (K Z Q : C) :
    HasKernel (projectionThenCoprojection K Z Q).hom := sorry

/-- Stacks 05QU: the canonical projection-coprojection arrow has a cokernel. -/
@[stacks 05QU]
instance (priority := 100) hasCokernel_projectionThenCoprojection (K Z Q : C) :
    HasCokernel (projectionThenCoprojection K Z Q).hom := sorry

namespace IsProjectionThenCoprojection

/-- Stacks 05QU: biproduct projection-coprojection normal form is preserved
when the arrow is replaced by an isomorphic arrow. -/
@[stacks 05QU]
theorem of_iso {f g : Arrow C} (hg : IsProjectionThenCoprojection g) (e : f ≅ g) :
    IsProjectionThenCoprojection f := sorry

/-- Stacks 05QU: an arrow in biproduct projection-coprojection normal form has
a kernel. -/
@[stacks 05QU]
theorem hasKernel {f : Arrow C} (hf : IsProjectionThenCoprojection f) :
    HasKernel f.hom := sorry

/-- Stacks 05QU: an arrow in biproduct projection-coprojection normal form has
a cokernel. -/
@[stacks 05QU]
theorem hasCokernel {f : Arrow C} (hf : IsProjectionThenCoprojection f) :
    HasCokernel f.hom := sorry

end IsProjectionThenCoprojection

end CategoryTheory.Arrow
