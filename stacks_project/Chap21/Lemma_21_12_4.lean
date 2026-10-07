module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology.UnderlyingComparison
import StacksCheckRecall

@[expose] public section

open SheafOfModules.Cohomology

/- Lemma 21.12.4 (03FD) identifies cohomology of the underlying additive sheaf of a module
sheaf with module `Ext`, both globally and after localizing at an object of the site. -/

@[stacks 03FD "global comparison"]
#check @underlying_isomorphic

@[stacks 03FD "comparison over an object"]
#check @underlyingOver_isomorphic
