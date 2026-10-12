/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.CatCommSq
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.29.8: compatibility of a derived pushforward with an exact forgetful functor is a
2-commutative square of derived functors.  Its consumable datum is `CatCommSq.iso`; the class
records the coherent square.  An equality of underived functors by itself is not concrete derived
comparison data, so it must not be installed as a fabricated global instance.
-/
@[stacks 0FTW] #check @CategoryTheory.CatCommSq.iso
#check @CategoryTheory.CatCommSq
#check @CategoryTheory.Functor.RightDerived.Cochain.functor
#check @CategoryTheory.Functor.mapDerivedCategory
