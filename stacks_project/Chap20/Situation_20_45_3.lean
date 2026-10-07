module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Situation 20.45.3: an open-family derived gluing datum assigns a derived module to every chosen
open and coherent restriction isomorphisms along inclusions.  A realization is an ambient derived
module together with compatible local identifications.  Negative self-Ext vanishing is expressed
using the global `DerivedExt` notation owned by ReasLib.
-/

@[stacks 0D67 "Situation 20.45.3: derived gluing data on an open family"]
#check @OpenFamily

@[stacks 0D67 "open-family negative self-Ext vanishing"]
#check @OpenFamily.NegativeSelfExtVanishing
@[stacks 0D67 "open-family local isomorphism data"]
#check @OpenFamily.LocalIso
@[stacks 0D67 "open-family realization predicate"]
#check @OpenFamily.IsRealization
@[stacks 0D67 "open-family realization object"]
#check @OpenFamily.Realization
@[stacks 0D67 "open-family realizes predicate"]
#check @OpenFamily.Realizes
@[stacks 0D67 "open-family realization existence predicate"]
#check @OpenFamily.HasRealization
@[stacks 0D67 "open-family realization existence iff"]
#check @OpenFamily.realizes_iff_exists
@[stacks 0D67 "open-family realization commutative square"]
#check @OpenFamily.IsRealization.commSq
@[stacks 0D67 "open-family realization equality"]
#check @OpenFamily.IsRealization.w
@[stacks 0D67 "open-family realization compatibility square"]
#check @OpenFamily.Realization.commSq
@[stacks 0D67 "compatible realization isomorphism"]
#check @OpenFamily.IsCompatibleIso
@[stacks 0D67 "compatible realization isomorphism square"]
#check @OpenFamily.IsCompatibleIso.commSq
@[stacks 0D67 "compatible realization isomorphism equality"]
#check @OpenFamily.IsCompatibleIso.w

end
