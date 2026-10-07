module

public import ReasLib.Algebra.Category.ModuleCat.ExteriorAlgebra
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered colimits of exterior algebras

Unlike tensor and symmetric algebras, the exterior algebra is not left
adjoint to the plain forgetful functor from associative algebras.  Filtered
colimit preservation is therefore exposed directly at its correct strength.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgCat.exteriorAlgebra

variable (R : Type u) [CommRing R]

/-- Exterior algebras preserve filtered colimits in a universe containing
the scalar ring. -/
@[stacks 00DQ "exterior algebras preserve filtered colimits"]
noncomputable instance preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{v, v}
      (AlgCat.exteriorAlgebra.{u, max u v} R) := sorry

/-- Exterior algebras preserve preorder-indexed directed colimits, including
the empty indexing preorder. -/
@[stacks 00DQ "exterior algebras preserve directed colimits"]
noncomputable instance preservesDirectedColimits
    {I : Type v} [Preorder I] [IsDirectedOrder I] :
    PreservesColimitsOfShape I
      (AlgCat.exteriorAlgebra.{u, max u v} R) := sorry

end AlgCat.exteriorAlgebra
