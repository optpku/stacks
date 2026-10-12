/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.Computation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Example 21.39.3 (08PH): a functor of categories and a coefficient morphism induce maps on the
explicit bar complexes and on category homology. -/
@[stacks 08PH "category homology simplicial map"]
#check @CategoryTheory.CategoryHomology.simplicialMap

@[stacks 08PH "category homology bar complex map"]
#check @CategoryTheory.CategoryHomology.complexMap

@[stacks 08PH "augmented category-homology bar map"]
#check @CategoryTheory.CategoryHomology.Bar.augmentedMapOfFunctor

@[stacks 08PH "bar complex map and augmentation compatibility"]
#check @CategoryTheory.CategoryHomology.Bar.chainAugmentation_map

@[stacks 08PH "category homology map from the bar construction"]
#check @CategoryTheory.CategoryHomology.Bar.map

@[stacks 08PH "zeroth bar map and colimit compatibility"]
#check @CategoryTheory.CategoryHomology.Bar.zeroMap_map

@[stacks 08PH "derived-colimit category homology companion map"]
#check @CategoryTheory.CategoryHomology.map

@[stacks 08PH "derived category homology map computed by the bar map"]
#check @CategoryTheory.CategoryHomology.map_isomorphic_barMap

@[stacks 08PG "bar category homology coefficient functor map formula"]
#check @CategoryTheory.CategoryHomology.Bar.coefficientFunctor_map

@[stacks 08PF "derived category homology coefficient functor map formula"]
#check @CategoryTheory.CategoryHomology.coefficientFunctor_map
