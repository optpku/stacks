/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Factorization
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.Factorization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.LocallyRingedSpace

/- Lemma 26.4.6 (1): factorization through an associated closed subspace is equivalent to
vanishing of the pulled-back ideal map. -/
@[stacks 01HP] #check ClosedSubspace.IsAssociated.exists_lift_iff
#check ClosedSubspace.IsAssociated.exists_lift
#check ClosedSubspace.IsAssociated.pullbackMap_eq_zero

/- The canonical ideal-quotient realization remains the lower-level factorization owner. -/
#check IdealQuotient.liftOfVanishing
#check IdealQuotient.liftOfVanishing_comp_ι
#check IdealQuotient.hom_ext
#check IdealQuotient.ι_mono
#check IdealQuotient.existsUnique_lift_iff_le_kernel

/- Lemma 26.4.6 (2): the factorization supplied by the vanishing criterion is unique. -/
@[stacks 01HP "unique factorization"]
#check ClosedSubspace.IsAssociated.existsUnique_lift
#check ClosedSubspace.IsAssociated.existsUnique_lift_iff

end AlgebraicGeometry.LocallyRingedSpace
