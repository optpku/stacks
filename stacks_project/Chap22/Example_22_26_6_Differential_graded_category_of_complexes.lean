module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory

universe u v

variable (C : Type u) [Category.{v} C] [Preadditive C]

/- Example 22.26.6 (Differential graded category of complexes) (09L9): cochain complexes in a
preadditive category form a differential graded category over `ℤ`, whose degree-`n` morphisms are
homogeneous cochains of degree `n`. -/
@[stacks 09L9] #check
  (CategoryTheory.CochainComplex.complexesDifferentialGradedCategory C :
    DifferentialGradedCategory ℤ (CochainComplex C ℤ))
#check @CategoryTheory.CochainComplex.complexesDifferentialGradedCategory_hom
