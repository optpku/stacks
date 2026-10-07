module

public import stacks_project.Chap48.Lemma_48_2_5
public import stacks_project.Chap48.Lemma_48_20_6_NormalizedRelative

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/-- A dualizing complex in the closed derived category sense is dualizing in the
scheme-local sense used by coherent duality. -/
theorem ofModuleDerived {X : Scheme.{u}} [IsLocallyNoetherian X]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsDualizingComplex K H) :
    Scheme.IsDualizingComplex K := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
