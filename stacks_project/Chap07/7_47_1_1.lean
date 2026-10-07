module

public import Mathlib.CategoryTheory.Sites.Sieves
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 7.47.1.1: a sieve `S` on `U` is a collection of subsets `S(T) ⊂ Mor_C(T, U)` whose only extra
rule is closure under precomposition: if `(α : T ⟶ U) ∈ S(T)` and `g : T' ⟶ T`, then
`(α ∘ g : T' ⟶ U) ∈ S(T')`. This is the mathlib field `Sieve.downward_closed`, with diagrammatic
composition `g ≫ α` in place of `α ∘ g`. -/
@[stacks 00YY] #check @Sieve.downward_closed
