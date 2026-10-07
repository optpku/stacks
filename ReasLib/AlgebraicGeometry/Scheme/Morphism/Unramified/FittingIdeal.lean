module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.LocalCriterion

/-!
# The non-unramified locus and the Fitting ideal of relative differentials

The non-unramified locus of a locally finite type morphism is the support of the zeroth Fitting
ideal sheaf of its relative differentials.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite type morphism, the support of the zeroth Fitting ideal sheaf of its
relative differentials is exactly the locus where the morphism is not unramified. -/
theorem fittingIdealSheaf_differentials_support_eq_nonUnramifiedAtLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 0).support : Set X) =
      {x : X | ¬ f.UnramifiedAt x} := sorry

end AlgebraicGeometry.Scheme.Hom
