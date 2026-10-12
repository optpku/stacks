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

/- 7.49.3.1: the sieve S'' on U is defined by the membership rule that
f : T ⟶ U lies in S''(T) iff there exist V, α : V ⟶ U in S(V), and
g : T ⟶ V in the refinement sieve S_{V,α}(T) with f = α ∘ g. This is the
sieve Sieve.bind S R obtained by binding S with the sieve-valued family
R α = S_{V,α}. Source composition f = α ∘ g is BindStruct.fac : g ≫ α = f. -/
@[stacks 00ZK] #check @Sieve.bind

#check @Sieve.BindStruct
#check @Presieve.BindStruct.bind
