module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Locus.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalCriterion

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat, locally finitely presented morphism whose nonempty fibres are equidimensional
of dimension `d`, the support of the `d`th Fitting ideal sheaf of relative differentials is the
complement of the smooth locus. -/
theorem fittingIdealSheaf_differentials_support_eq_compl_smoothLocus
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [Flat f] [LocallyOfFinitePresentation f]
    [RelativeDimension f d] :
    ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) d).support : Set X) =
      (f.smoothLocus : Set X)ᶜ := sorry

end AlgebraicGeometry.Scheme.Hom
