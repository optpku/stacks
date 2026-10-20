module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.7.1

Injective module sheaves and cohomology on a localized ringed site are owned by the generic
`SheafOfModules.Localization` API.  The chapter entry keeps only the source-facing recalls.
-/

open SheafOfModules.Localization
open SheafOfModules.Localization.Cohomology

@[stacks 03F3 "localized restriction preserves injectives"]
#check @restriction_preservesInjectiveObjects

@[stacks 03F3 "restriction of an injective module sheaf"]
#check @injective_restriction

@[stacks 03F3 "module-valued cohomology on a localized site"]
#check @atObject_isomorphic

@[stacks 03F3 "underlying cohomology at the terminal slice object"]
#check @atTerminal_isomorphic

@[stacks 03F3 "cohomology over an object as localized global cohomology"]
#check @global_isomorphic
