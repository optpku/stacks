/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopCat TopCat.Sheaf

/- 20.2.0.2 (0713): the `i`th higher direct image of an abelian sheaf is canonically isomorphic
to the `i`th homology object of the pushforward of any chosen injective resolution.  The reusable
owner is the actual `Iso`, rather than a proposition-level `IsIsomorphic` wrapper. -/
@[stacks 0713 "higher direct image from an injective resolution"]
#check @TopCat.Sheaf.HigherDirectImage.isoHomologyPushforward

#check @CategoryTheory.InjectiveResolution.isoRightDerivedObj

end
