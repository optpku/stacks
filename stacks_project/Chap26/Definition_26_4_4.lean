/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Reusable predicate and specification for comparing any realization of an associated closed
subspace. -/
#check LocallyRingedSpace.ClosedSubspace.IsAssociated
#check LocallyRingedSpace.ClosedSubspace.IsAssociated.idealSheafIso
#check LocallyRingedSpace.ClosedSubspace.isAssociated_iff_spec
#check LocallyRingedSpace.ClosedSubspace.IsAssociated.spec

/- Definition 26.4.4: quotienting the structure sheaf by a locally generated ideal gives its
associated closed subspace, together with the canonical inclusion into the ambient space. -/
@[stacks 01HN] #check LocallyRingedSpace.IdealQuotient.space
@[stacks 01HN] #check LocallyRingedSpace.IdealQuotient.ι
@[stacks 01HN] #check LocallyRingedSpace.IdealQuotient.ι_isAssociated

/- Concrete presentation and computation API for the canonical ideal quotient. -/
#check LocallyRingedSpace.IdealQuotient.presentation
#check LocallyRingedSpace.IdealQuotient.presentation_sheaf
#check LocallyRingedSpace.IdealQuotient.presentation_projection
#check LocallyRingedSpace.IdealQuotient.ι_toHom
#check LocallyRingedSpace.IdealQuotient.ι_base
#check LocallyRingedSpace.IdealSubobject.IsLocallyGeneratedBySections
#check LocallyRingedSpace.IdealSubobject.isLocallyGeneratedBySections_iff
#check LocallyRingedSpace.IdealQuotient.kernelIdealSubobject_ι
