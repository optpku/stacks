module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Connected.EtaleNeighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The canonical map from a proper scheme morphism to its relative normalization is
proper. -/
instance instIsProperToNormalizationOfProper (f : X ⟶ S) [IsProper f] :
    IsProper f.toNormalization := sorry

/-- For a proper morphism to a locally Noetherian scheme, the structural morphism from
the relative normalization is finite. -/
instance instIsFiniteFromNormalizationOfProper
    (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] :
    IsFinite f.fromNormalization := sorry

/-- For every proper scheme morphism, the canonical map to its relative normalization
has geometrically connected fibres. -/
instance instGeometricallyConnectedToNormalizationOfProper
    (f : X ⟶ S) [IsProper f] :
    GeometricallyConnected f.toNormalization := sorry

end AlgebraicGeometry.Scheme.Hom
