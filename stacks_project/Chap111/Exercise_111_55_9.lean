module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Surjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Exercise 111.55.9: there exists a morphism from the complex affine line to the complex
projective line that is surjective on underlying scheme points. -/
@[stacks 07DN] #check
  (AlgebraicGeometry.ProjectiveLine.exists_surjective_from_affineLine :
    ∃ f : AlgebraicGeometry.ProjectiveLine.affineLine ℂ ⟶
      AlgebraicGeometry.ProjectiveLine.scheme ℂ, AlgebraicGeometry.Surjective f)
