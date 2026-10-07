module

public import ReasLib.CategoryTheory.Fibered.Stack.StronglyCartesianSubcategory
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.5.3: if `p : S ⥤ C` is a stack over `(C, J)`, then its restriction to the
strongly cartesian morphisms is a stack in groupoids over `(C, J)`. -/
@[stacks 03YI]
#check @Functor.IsStronglyCartesian.projection_isStackInGroupoids

#check @StackOver.associatedGroupoid

/- The stack part and the canonical groupoid-fibered projection are independently reusable. The
following `map` API is only the object-and-`1`-morphism action; arbitrary vertical `2`-morphisms do
not necessarily restrict to the strongly-cartesian subcategories. -/
#check @StackOver.associatedGroupoid.toGroupoids
#check @StackOver.associatedGroupoid.p
#check @StackOver.associatedGroupoid.inclusion
#check @StackOver.associatedGroupoid.inclusion.toMor
#check @StackOver.associatedGroupoid.map
#check @StackOver.associatedGroupoid.map.toGroupoidsMor
#check @StackOver.associatedGroupoid.map_id
#check @StackOver.associatedGroupoid.map_comp
#check @StackOver.associatedGroupoid.map.toStackOver
#check @StackOver.associatedGroupoid.map.toStackOver.toMor
#check @StackOver.associatedGroupoid.inclusion_naturality
#check @FiberedCategoryOver.associatedGroupoid
#check @FiberedCategoryOver.associatedGroupoid.inclusion
#check @FiberedCategoryOver.associatedGroupoid.map
#check @FiberedCategoryOver.associatedGroupoid.inclusion_naturality
#check @FiberedCategoryOver.associatedGroupoid.map_id
#check @FiberedCategoryOver.associatedGroupoid.map_comp
#check @CartesianBasedFunctor.AssociatedGroupoid.functor
#check @CartesianBasedFunctor.AssociatedGroupoid.basedFunctor
#check @MorphismProperty.WideSubcategory.restrict
#check @Functor.IsStronglyCartesian.projection_isStackOnSite
#check @Functor.IsStronglyCartesian.projectionInGroupoids

end CategoryTheory
