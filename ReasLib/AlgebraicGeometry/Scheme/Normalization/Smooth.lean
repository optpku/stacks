module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Smooth

/-!
# Normalization and smooth morphisms

This file compares the normalization of the source of a smooth morphism with the pullback of the
normalization of its target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization

/-- For a smooth morphism, the normalization of the source is uniquely isomorphic over the source
to the pullback of the normalization of the target. -/
theorem existsUniquePullbackIsoOfSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    -- Local instance justification (proof-local temporary data): needed only to form X.normalization.
    letI : HasFiniteIrreducibleComponentsOnCompactOpens X :=
      HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f
    ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
      e.hom ≫ pullback.snd _ _ = X.normalizationTo := sorry

end AlgebraicGeometry.Scheme.Normalization
