module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
public import ReasLib.FieldTheory.Cr

@[expose] public section

universe u

namespace BrauerGroup

/-- Every Brauer class over a C₁ field is the neutral class. -/
theorem eq_one_of_isCr {K : Type u} [Field K] (hC1 : Field.IsCr K 1) (A : Br(K)) : A = 1 := sorry

end BrauerGroup

end
