module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.WellOrdered

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Lemma 20.45.7: coherent derived modules on a continuous increasing well-ordered open cover, with
vanishing negative self-Ext, admit an ambient realization.  The indexed owner retains repeated
values of the open family and bundles monotonicity, transition isomorphisms, and their cocycle law
as `WellOrdered.System`.
-/

@[stacks 0D6B "Lemma 20.45.7: derived gluing along a well-ordered open cover"]
#check @WellOrdered.System.existsRealization

@[stacks 0D6B "well-ordered open-family system"]
#check @WellOrdered.System
@[stacks 0D6B "well-ordered negative self-Ext vanishing"]
#check @WellOrdered.System.NegativeSelfExtVanishing
@[stacks 0D6B "well-ordered local isomorphism"]
#check @WellOrdered.System.LocalIso
@[stacks 0D6B "well-ordered realization predicate"]
#check @WellOrdered.System.IsRealization
@[stacks 0D6B "well-ordered realization object"]
#check @WellOrdered.System.Realization
@[stacks 0D6B "well-ordered realization existence predicate"]
#check @WellOrdered.System.HasRealization
@[stacks 0D6B "well-ordered realization existence iff"]
#check @WellOrdered.System.hasRealization_iff_exists
@[stacks 0D6B "well-ordered realization compatibility square"]
#check @WellOrdered.System.Realization.commSq

end
