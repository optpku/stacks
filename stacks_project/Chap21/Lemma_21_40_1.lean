module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Computation
import StacksCheckRecall

@[expose] public section

/- Lemma 21.40.1 (08PI): for a presheaf on the total category of a fibred category, the
fiberwise bar-complex homology objects, their cartesian restriction maps, the resulting presheaf
and sheafification, and the associated-sheaf comparison are reusable owners in
`ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar`.  The projective-resolution presentation
is a separately tagged comparison view. This chapter entry is recall-only and introduces no
second API. -/
@[stacks 08PI "fiber category homology object"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.homology
@[stacks 08PI "fiber homology restriction map"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.restriction
@[stacks 08PI "fiber category homology presheaf"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.presheaf
@[stacks 08PH "fiber homology coefficient map"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.map
@[stacks 08PI "fiber category homology sheaf"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.sheaf
@[stacks 08PI "fiber category homology sheaf of a sheaf"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.sheafOfSheaf
@[stacks 08PI "fiber homology associated-sheaf component"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.associatedMapApp
@[stacks 08PI "fiber homology associated-sheaf naturality"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.associatedMap_naturality
@[stacks 08PI "fiber homology associated-sheaf map"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.associatedMap
@[stacks 08PI "fiber homology associated-sheaf comparison"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.sheafAssociatedHom
@[stacks 08PI "fiber homology sheafification invariance"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.sheafAssociatedHom_isIso

@[stacks 08PG "projective model of fiber category homology"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Derived.homology
@[stacks 08PG "derived and bar fiber homology presheaf comparison"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Computation.presheaf_isomorphic_bar
@[stacks 08PG "derived and bar fiber homology presheaf functor comparison"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Computation.presheafFunctor_isomorphic_bar
@[stacks 08PI "bar fiber homology coefficient functor"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.presheafFunctor
@[stacks 08PI "bar fiber homology coefficient functor object formula"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.presheafFunctor_obj
@[stacks 08PI "bar fiber homology coefficient functor map formula"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Bar.presheafFunctor_map
@[stacks 08PG "derived and bar fiber homology sheaf comparison"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Computation.sheaf_isomorphic_bar
@[stacks 08PG "derived and bar fiber homology sheaf functor comparison"]
#check @CategoryTheory.FiberedCategoryOver.FiberHomology.Computation.sheafFunctor_isomorphic_bar
