module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowCohomology

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 42.34.1: For `X` locally of finite type over the universally catenary
dimensioned base `(S, δ)`, the Chow cohomology ring `A⁎(X)` is graded by
`Aⁿ(X ⟶ X)`.  No commutativity assertion is made. -/
@[stacks 0B7E] #check (AlgebraicGeometry.ChowCohomology.ring :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p],
    Type (u + 1))
