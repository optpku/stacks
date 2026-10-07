module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Graded
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.RestrictScalars
public import ReasLib.RingTheory.GradedAlgebra.DegreeOne
public import stacks_project.Chap10.Proposition_10_58_7.DegreeOneQuotients
import StacksCheckRecall

/-!
# Proposition 10.58.7 support index

This aggregate exports only canonical/reusable support surfaces.  The former homogeneous-quotient
and kernel proof scaffolding used `Submodule S M` for graded pieces and is intentionally excluded
until expressed through the shared `Submodule R M` quotient APIs.
-/

@[expose] public section

@[stacks 00K1 "Proposition 10.58.7 reusable support index"]
#check @CategoryTheory.ModuleCat.K0.gradedPieceClass_of_isNoetherian_isNumericalPolynomial
