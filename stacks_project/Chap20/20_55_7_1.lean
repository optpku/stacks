module

public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein
import StacksCheckRecall

@[expose] public section

/- 20.55.7.1 (0GT7): the Bockstein factorization is the canonical factorization of the integral
connecting operator through the scalar-restricted quotient row. -/
@[stacks 0GT7 "factorization of the Bockstein operator"]
#check @HomologicalComplex.Bockstein.integralOperator_comp_reduction

/- The proof-independent formulation with explicitly supplied short-exact rows. -/
@[stacks 0GT7 "Bockstein factorization from short-exact rows"]
#check @HomologicalComplex.Bockstein.integralOperatorOfShortExact_comp_reduction

/- The underlying naturality mechanism for connecting morphisms. -/
#check @HomologicalComplex.HomologySequence.δ_naturality

end
