module

public import ReasLib.AlgebraicGeometry.Hilbert.Sheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 44.2.1: for a morphism of schemes `X ⟶ S` and `d : ℕ`, the functor
`Hilbert.functor X d` is a sheaf for the fpqc topology on schemes over `S`. -/
@[stacks 0B95] #check
  (AlgebraicGeometry.Hilbert.functor_isSheaf_fpqc :
    ∀ {S : Scheme.{u}} (X : Over S) (d : ℕ),
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (AlgebraicGeometry.Hilbert.functor X d))
