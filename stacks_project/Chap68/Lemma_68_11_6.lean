module

public import stacks_project.Chap68.Lemma_68_11_6_Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.11.6: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`. Let `x` be
a point of `X`. The category of elementary étale neighbourhoods of `(X, x)` is cofiltered. -/
@[stacks 0BGV] #check
  (EtaleNeighborhood.Elementary.instIsCofiltered :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
      IsCofiltered (EtaleNeighborhood.Elementary X x))
