module

public import ReasLib.AlgebraicGeometry.SqrtNegT
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.34.2: there is no nonempty open `U ⊆ S` and morphism
`σ : U.toScheme ⟶ X` such that `σ ≫ π = U.ι`. -/
@[stacks 0295] #check
  (AlgebraicGeometry.SqrtNegT.not_exists_rational_section :
    ¬ ∃ (U : AlgebraicGeometry.SqrtNegT.base.Opens), Nonempty U.toScheme ∧
      ∃ σ : U.toScheme ⟶ AlgebraicGeometry.SqrtNegT.totalSpace,
        σ ≫ AlgebraicGeometry.SqrtNegT.toBase = U.ι)
