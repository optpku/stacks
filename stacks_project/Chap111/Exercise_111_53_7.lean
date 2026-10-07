module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Finite
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/- Exercise 111.53.7 -/
@[stacks 069X] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_closedImmersion_of_finite :
    {R S : CommRingCat.{u}} → {f : R ⟶ S} → f.hom.Finite →
      ∃ (n : ℕ) (i : Spec S ⟶ ProjectiveSpace.scheme R n),
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec R n = Spec.map f)

end AlgebraicGeometry
