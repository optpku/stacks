module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Profinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Definition 58.6.1: for a connected scheme `X` and geometric point `xbar`,
the fundamental group is `Aut` of the finite étale fiber functor, with its
canonical profinite topology. -/
@[stacks 0BNC] #check
  (AlgebraicGeometry.Scheme.profiniteFundamentalGroup :
    ∀ {X : Scheme.{u}} [ConnectedSpace X] {K : Type u} [Field K] [IsAlgClosed K],
      (Spec (.of K) ⟶ X) → ProfiniteGrp.{u + 1})
