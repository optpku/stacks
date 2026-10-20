module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.MaximumLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Affine maximum loci of positive weightings
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a quasi-finite finitely presented morphism between affine schemes, the locus where the
fibre integral of a positive weighting attains a specified greatest value is affine. -/
theorem IsWeighting.isAffineOpen_fiberIntegralMaximumLocus
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine X] [IsAffine Y]
    [QuasiFinite f] [FinitePresentation f] {w : X → ℤ} (hw : f.IsWeighting w)
    (h_pos : ∀ x : X, 0 < w x) (d : ℤ)
    (h_max : IsGreatest
      (Set.range (f.fiberIntegral (tendstoCofinite_of_compactSource f) w)) d) :
    IsAffineOpen (hw.fiberIntegralMaximumLocus h_pos d h_max) := sorry

end AlgebraicGeometry.Scheme.Hom
