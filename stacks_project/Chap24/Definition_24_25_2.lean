module

public import ReasLib.CategoryTheory.Functor.Injective
import StacksCheckRecall

/-!
# Definition 24.25.2

Graded injectivity is the canonical inverse-image object property
`CategoryTheory.Functor.IsInjectiveObj` for the forgetful functor to graded modules.
-/

@[expose] public section

/- Definition 24.25.2 (0FSP): a differential graded module is graded injective precisely when its image
under the forgetful functor to graded modules is injective. -/
@[stacks 0FSP] #check @CategoryTheory.Functor.IsInjectiveObj

#check @CategoryTheory.Functor.isInjectiveObj_iff
