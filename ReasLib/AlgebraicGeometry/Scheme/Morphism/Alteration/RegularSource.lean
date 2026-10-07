module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsAlteration

/-- For a Noetherian integral scheme admitting an alteration from a regular integral scheme,
the normalization morphism of the target is finite. -/
theorem isFinite_normalizationTo
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral Y] [IsIntegral X]
    (f : X ⟶ Y) [IsAlteration f] [Scheme.Regular X] :
    IsFinite Y.normalizationTo := sorry

/-- For a Noetherian integral scheme admitting an alteration from a regular integral scheme,
the target contains a dense open subscheme that is regular. -/
theorem exists_dense_open_regular
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral Y] [IsIntegral X]
    (f : X ⟶ Y) [IsAlteration f] [Scheme.Regular X] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ Scheme.Regular U.toScheme := sorry

end AlgebraicGeometry.IsAlteration
