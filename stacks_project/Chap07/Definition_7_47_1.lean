module

public import Mathlib.CategoryTheory.Sites.Sieves
import ReasLib.CategoryTheory.Sites.Sieve.Subfunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/- Definition 7.47.1: for a category C and an object U, a sieve S on U is a
subpresheaf S ⊂ h_U. The canonical identification is
`Sieve.subfunctorEquiv : Sieve U ≃ Subfunctor (yoneda.obj U)`. -/
@[stacks 00YX] #check
  (CategoryTheory.Sieve.subfunctorEquiv :
    (U : C) → CategoryTheory.Sieve U ≃ CategoryTheory.Subfunctor (CategoryTheory.yoneda.obj U))

#check CategoryTheory.Sieve.functor
#check CategoryTheory.Sieve.functorInclusion
#check CategoryTheory.Sieve.functorInclusion_is_mono
#check CategoryTheory.Sieve.sieveOfSubfunctor
#check CategoryTheory.Sieve.sieveOfSubfunctor_functorInclusion
