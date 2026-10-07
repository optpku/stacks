module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalPolynomialSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry.Scheme.Hom.FiniteType

noncomputable section

namespace UniversalPolynomialSystem

#check MultiIndex
#check MultiIndex.sum_le
#check MultiIndex.toFinsupp
#check MultiIndex.toFinsupp_apply
#check CoefficientRing
#check PolynomialRing
#check equation
#check relationIdeal
#check CoordinateRing
#check baseScheme
#check familyScheme
#check projection

/- Example 49.10.5 -/
@[stacks 0FK8]
#check (UniversalPolynomialSystem.quasiFiniteOpen :
  ∀ n d : ℕ+, (UniversalPolynomialSystem.familyScheme n d).Opens)

#check AlgebraicGeometry.Scheme.Hom.FiniteType.mem_quasiFiniteLocus
#check AlgebraicGeometry.Scheme.Hom.FiniteType.locallyQuasiFinite_quasiFiniteLocus
#check UniversalPolynomialSystem.le_quasiFiniteOpen_iff

end UniversalPolynomialSystem
