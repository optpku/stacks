/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.LocallyRingedSpace

/- Lemma 26.4.5: a closed immersion is uniquely isomorphic over the target to the associated
closed subspace defined by its kernel ideal. -/
@[stacks 01HO] #check IsClosedImmersion.existsUnique_iso_to_associated
#check ClosedSubspace.IsAssociated.toIdealQuotient
#check ClosedSubspace.IsAssociated.toIdealQuotient_ι
#check ClosedSubspace.IsAssociated.toIdealQuotient_unique
#check ClosedSubspace.IsAssociated.toIdealQuotient_isIso
#check ClosedSubspace.IsAssociated.existsUnique_iso
#check ClosedSubspace.IsAssociated.existsUnique_hom
#check ClosedSubspace.IsAssociated.overHom_subsingleton
#check ClosedSubspace.IsAssociated.overIso_subsingleton

end AlgebraicGeometry.LocallyRingedSpace
