/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 20.14.1: a morphism `G ⟶ F(K)` of bounded-below cochain complexes induces the
canonical morphism `G ⟶ RF(K)` in the bounded-below derived category.  For module pushforward on
ringed spaces, specialize `F` to `f _*`. -/
@[stacks 01F8]
#check @Functor.RightDerived.Bounded.fromCochainMap

#check @Functor.RightDerived.Bounded.fromCochainMap_natural
