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

/- Example 21.39.2 (08PG): category homology is computed by the explicit bar complex on
composable arrows. -/
@[stacks 08PG "category homology bar complex"]
#check @CategoryTheory.CategoryHomology.simplicialObject

@[stacks 08PG "category homology bar complex"]
#check @CategoryTheory.CategoryHomology.complex

@[stacks 08PG "canonical bar colimit augmentation"]
#check @CategoryTheory.CategoryHomology.Bar.colimitAugmentation

@[stacks 08PG "category-homology bar chain augmentation"]
#check @CategoryTheory.CategoryHomology.Bar.chainAugmentation

@[stacks 08PG "zeroth bar homology is presheaf colimit"]
#check @CategoryTheory.CategoryHomology.Bar.zeroIso

@[stacks 08PG "category homology bar delta functor"]
#check @CategoryTheory.CategoryHomology.Bar.deltaFunctor

@[stacks 08PG "universal category-homology comparison with the bar delta functor"]
#check @CategoryTheory.CategoryHomology.Bar.universalIso

@[stacks 08PG "category homology bar complex computation"]
#check @CategoryTheory.CategoryHomology.isomorphic_homology_complex

@[stacks 08PF "derived category homology coefficient functor"]
#check @CategoryTheory.CategoryHomology.coefficientFunctor

@[stacks 08PF "derived category homology coefficient functor object formula"]
#check @CategoryTheory.CategoryHomology.coefficientFunctor_obj

@[stacks 08PG "bar category homology coefficient functor"]
#check @CategoryTheory.CategoryHomology.Bar.coefficientFunctor

@[stacks 08PG "bar category homology coefficient functor object formula"]
#check @CategoryTheory.CategoryHomology.Bar.coefficientFunctor_obj
