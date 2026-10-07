module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import ReasLib.CategoryTheory.Homology.DoubleComplex.DegreewiseSplit
public import ReasLib.CategoryTheory.Homology.DoubleComplex.HomotopyTotal.Shift

/-!
# Exactness of totalization on homotopy categories

Direct totalization sends the degreewise-split normal forms for distinguished triangles to
degreewise-split distinguished triangles. Exactness of flipped totalization is equivalent through
the shift-compatible total-flip comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe v u

namespace HomologicalComplex₂.HomotopyTotal

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasCountableCoproducts C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- Direct totalization is an exact functor between homotopy categories. -/
@[stacks 0G6D "exactness of direct totalization"]
noncomputable instance directIsTriangulated : (direct C).IsTriangulated := sorry

/-- Flipped totalization is an exact functor between homotopy categories. -/
@[stacks 0G6D "exactness of flipped totalization"]
noncomputable instance flippedIsTriangulated : (flipped C).IsTriangulated := sorry

end HomologicalComplex₂.HomotopyTotal
