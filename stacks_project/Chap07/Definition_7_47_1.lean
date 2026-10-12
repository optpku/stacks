/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sieves
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.47.1: for a category C and an object U, a sieve S on U is a
subpresheaf S ⊂ h_U. Equivalently, S assigns to each T a subset S(T) ⊆ Hom(T, U)
closed under precomposition. The canonical owner is `Sieve`; the subpresheaf
packaging is `Sieve.functor` with the mono `Sieve.functorInclusion` into
`yoneda.obj U`. -/
@[stacks 00YX] #check CategoryTheory.Sieve

#check @Sieve.functor
#check @Sieve.functorInclusion
#check Sieve.functorInclusion_is_mono
#check @Sieve.sieveOfSubfunctor
#check @Sieve.sieveOfSubfunctor_functorInclusion
