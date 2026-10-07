module

public import ReasLib.Algebra.Module.Finite.FilteredColimit
import StacksCheckRecall

/-!
# Finite modules and filtered colimits

@stack 0G8N
-/

@[expose] public section

@[stacks 0G8N "finite modules detect equality in filtered colimits"]
#check @Module.Finite.iff_colimitPost_injective

@[stacks 0G8N "finite module predicate"]
#check @Module.Finite

@[stacks 0G8N "representable colimit comparison at a stage"]
#check @CategoryTheory.Limits.colimit_post_coyoneda_ι_app

@[stacks 0G8N "comparison criterion when the representable preserves the colimit"]
#check @CategoryTheory.Limits.colimitPost_bijective_of_preserves
