module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Effective
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 98.9.4: for a locally Noetherian scheme `S` and a category `X`
fibred in groupoids over `(Sch/S)_fppf`, a formal object `ξ = (R, ξ_n, f_n)` of
`X` is effective if it lies in the essential image of the approximation functor
`98.9.3.1`. -/
@[stacks 07X7] #check (AlgebraicGeometry.GroupoidsOver.FormalObject.IsEffective :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {X : AlgebraicGeometry.GroupoidsOver S},
    AlgebraicGeometry.GroupoidsOver.FormalObject X → Prop)
