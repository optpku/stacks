module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- An algebraic space locally of finite type over the base whose restricted
functor of points is naturally isomorphic to the compatible-triple functor
admits a solution of the contraction situation. -/
theorem nonempty_solutionFor_of_natIso (σ : ContractionSituation S)
    (X : AlgebraicSpace S) [LocallyOfFiniteType (SchemeRealization.toBase X)]
    (e : σ.functor ≅ homOnLocallyNoetherian X) :
    Nonempty (SolutionFor σ X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
