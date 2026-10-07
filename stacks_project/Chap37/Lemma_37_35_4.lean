module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.35.4: for a scheme `S` and a point `s : S`, the category of elementary
étale neighborhoods of `(S, s)` is cofiltered. -/
@[stacks 057B] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.instIsCofiltered :
    ∀ (S : Scheme.{u}) (s : S),
      IsCofiltered (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary S s))
