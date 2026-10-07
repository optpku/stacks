module

public import Mathlib.CategoryTheory.Sites.Sieves
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.47.4: for a category C, a morphism f : V ⟶ U, and a sieve S on U,
the pullback of S by f (also called the base change of S by f) is the sieve
S.pullback f on V whose members are the arrows α : T ⟶ V such that
α ∈ S.pullback f ↔ (α ≫ f) ∈ S. In source notation this is S ×_U V. The
return type Sieve V records that this is indeed a sieve. -/
@[stacks 00Z2] #check @Sieve.pullback

#check @Sieve.pullback_apply
