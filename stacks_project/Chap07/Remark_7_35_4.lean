module

public import ReasLib.CategoryTheory.Sites.Point.Localization.Pushforward
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.35.4

The nonexistence statement belongs to the reusable localization direct-image
API; this Chapter 7 entry is the source-facing warning.
-/

@[expose] public section

/- Remark 7.35.4 (04H5): the fiber formula for localization lower shriek has no analogue for the
localization direct image `j_{U,*}`. -/
@[stacks 04H5] #check @CategoryTheory.GrothendieckTopology.Point.Localization.Pushforward.not_forall_sheafFiber_isomorphic_sigma
