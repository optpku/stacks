module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.RestrictScalars
public import ReasLib.RingTheory.GradedAlgebra.DegreeOne
import StacksCheckRecall

@[expose] public section

/-! @stack 00K1 -/

/-!
# Proposition 10.58.7

The numerical-polynomial theorem is a reusable K0 result, so this chapter entry is a canonical
recall rather than a second theorem owner.
-/

/- API design: the exact theorem uses the source hypotheses, derives finite type inside the data
owner, and models pieces as `Submodule R M`.  The former induction helpers and chapter-long aliases
were removed because they added proof scaffolding rather than reusable semantics. -/

/- Proposition 10.58.7 (Tag 00K1): if the irrelevant ideal is generated in degree one, the
degree-wise K0 class function of a finite graded module is a numerical polynomial. -/
@[stacks 00K1]
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian_isNumericalPolynomial

/- Proposition 10.58.7 support: the source class function is the canonical Noetherian K0 owner. -/
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian

/- Proposition 10.58.7 support: restriction of scalars is a generic additive K0 map. -/
#check @CategoryTheory.ModuleCat.K0.restrictScalars
