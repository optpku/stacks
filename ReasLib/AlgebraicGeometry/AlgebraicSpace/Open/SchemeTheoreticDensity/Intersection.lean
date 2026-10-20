module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition

/-!
# Intersection of scheme-theoretically dense open subspaces

The intersection of two scheme-theoretically dense open subspaces of an
algebraic space is scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense

/-- Scheme-theoretic density of two open immersions implies scheme-theoretic
density of the inclusion of their intersection. -/
theorem of_inf {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    {ιU : U ⟶ X} {ιV : V ⟶ X} [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    (hU : IsSchemeTheoreticallyDense ιU)
    (hV : IsSchemeTheoreticallyDense ιV) :
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU) :=
  sorry

/-- The inclusion of the intersection of two scheme-theoretically dense open
subspaces is scheme-theoretically dense. -/
instance inf {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    (ιU : U ⟶ X) (ιV : V ⟶ X) [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    [IsSchemeTheoreticallyDense ιU] [IsSchemeTheoreticallyDense ιV] :
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU) :=
  of_inf inferInstance inferInstance

end AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense
