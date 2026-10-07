module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Variety.FunctionField

@[expose] public section

open CategoryTheory

universe u

/- Theorem 33.4.1: for a field `k`, varieties over `k` with dominant rational maps are
equivalent to the opposite category of finitely generated field extensions of `k`. -/
@[stacks 0BXN] #check
  (AlgebraicGeometry.VarietyDominantRationalMapCat.nonemptyEquivFinitelyGeneratedFieldExtensions :
    ∀ {k : Type u} [Field k],
      Nonempty
        (AlgebraicGeometry.VarietyDominantRationalMapCat k ≌
          (AlgebraicGeometry.FinitelyGeneratedFieldExtension.Cat k)ᵒᵖ))
