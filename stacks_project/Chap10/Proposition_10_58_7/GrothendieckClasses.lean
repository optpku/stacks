module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.RestrictScalars
public import ReasLib.RingTheory.GradedAlgebra.DegreeOne
import StacksCheckRecall

@[expose] public section

/-!
# Grothendieck classes for Proposition 10.58.7

Compatibility import surface for the canonical K0 and degree-one generation owners.
-/

/- API design: all former long chapter aliases were definitionally equal to these owners and added
no mathematical content.  This facade therefore exposes canonical checks only. -/

/- Proposition 10.58.7 support: the K0-valued function of homogeneous components. -/
@[stacks 00K1 "graded-piece class support"]
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass

/- Proposition 10.58.7 support: finite type is derived by the canonical Noetherian owner. -/
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian

/- Proposition 10.58.7 support: numerical-polynomiality under the degree-one span hypothesis. -/
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian_isNumericalPolynomial

/- Proposition 10.58.7 support: restriction of scalars on finite Grothendieck groups. -/
#check @CategoryTheory.ModuleCat.K0.restrictScalars
#check @CategoryTheory.ModuleCat.K0.finiteClass_restrictScalars

/- Proposition 10.58.7 support: a finite degree-one spanning witness. -/
#check @GradedAlgebra.exists_finset_span_degreeOne_eq_irrelevant
