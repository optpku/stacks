module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.BidegreeShift
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ)
variable [K.HasTotal (up ℤ)]

/- Remark 12.18.5 [0FLG]: the total complex of a bidegree shift is the total complex shifted by
the sum, with the second-direction Koszul sign on each antidiagonal summand. -/
@[stacks 0FLG]
#check HomologicalComplex₂.BidegreeShift.ι_totalIso_symm_hom_f K a b

/- The construction exposes both the canonical and inverse-facing comparison directions. -/
#check HomologicalComplex₂.BidegreeShift.totalIso K a b
#check (HomologicalComplex₂.BidegreeShift.totalIso K a b).symm
#check K.bidegreeShift a b
