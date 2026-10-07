module

import ReasLib.CategoryTheory.ObjectProperty.Retract.Lattice
import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.ObjectProperty

/- Definition 13.6.1: the source's saturated strictly full subcategories are modeled by the
canonical predicate expressing closure under retracts. -/
@[stacks 05RB] #check IsStableUnderRetracts

variable {C : Type u} [Category.{v} C] (P Q : ObjectProperty C)

/- Retract stability already implies closure under isomorphisms, so strict fullness is recovered
by typeclass search rather than stored as a second source-local condition. -/
section

variable [P.IsStableUnderRetracts]

#check (inferInstance : P.IsClosedUnderIsomorphisms)

end


/- The direct-summand condition composes pointwise; arbitrary intersections and unions are owned
by the same neutral lattice API. -/
section

variable [P.IsStableUnderRetracts] [Q.IsStableUnderRetracts]

#check (inferInstance : (P ⊓ Q).IsStableUnderRetracts)
#check (inferInstance : (P ⊔ Q).IsStableUnderRetracts)

end


end CategoryTheory.ObjectProperty
