module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- Under finite-presentation, flatness, and geometric reducedness hypotheses, the
structural morphism from the Stein factorization is finite. -/
instance instIsFiniteFromNormalizationOfFlatGeometricallyReduced
    (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f] [Flat f]
    [GeometricallyReduced f] :
    IsFinite f.fromNormalization := sorry

/-- Under finite-presentation, flatness, and geometric reducedness hypotheses, the
structural morphism from the Stein factorization is étale. -/
instance instEtaleFromNormalizationOfFlatGeometricallyReduced
    (f : X ⟶ S) [IsProper f] [Scheme.Hom.FinitePresentation f] [Flat f]
    [GeometricallyReduced f] :
    Etale f.fromNormalization := sorry

end AlgebraicGeometry.Scheme.Hom
