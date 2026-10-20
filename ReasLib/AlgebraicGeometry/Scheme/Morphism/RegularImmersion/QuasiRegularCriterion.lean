module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Ideal.QuasiRegular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# A conormal criterion for quasi-regular immersions

This file characterizes quasi-regular immersions using local finite presentation and the
finite-locally-free conormal and associated-graded criteria on a closed presentation.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsQuasiRegularImmersion

/-- An immersion satisfies the conormal criterion when it admits a closed presentation over an
open subscheme whose kernel ideal has finite locally free conormal module and polynomial
associated graded algebra. -/
def conormalCriterion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] : Prop :=
  ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
    IsClosedImmersion j ∧ (j ≫ U.ι = i) ∧
      RingedSpace.idealSheafConormalFiniteLocallyFreeCriterion j.kernelIdealSubobject ∧
        RingedSpace.idealSheafAssociatedGradedPolynomialCriterion j.kernelIdealSubobject

/-- An immersion is quasi-regular exactly when it is locally of finite presentation and admits
a closed presentation satisfying the conormal criterion. -/
theorem iff_locallyOfFinitePresentation_and_conormalCriterion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    IsQuasiRegularImmersion i ↔
      LocallyOfFinitePresentation i ∧ IsQuasiRegularImmersion.conormalCriterion i := sorry

end AlgebraicGeometry.IsQuasiRegularImmersion
