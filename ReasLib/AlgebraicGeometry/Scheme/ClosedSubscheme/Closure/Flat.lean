module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The inverse image of a retrocompact scheme-theoretically dense open under a flat
morphism is scheme-theoretically dense. -/
theorem schemeTheoreticallyDense_preimage_of_flat_of_isRetrocompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (V : Y.Opens)
    (hVretro : IsRetrocompact (V : Set Y)) (hVdense : schemeTheoreticallyDense V) :
    schemeTheoreticallyDense (f ⁻¹ᵁ V) := sorry

/-- The inverse image of a scheme-theoretically dense open under a flat, locally
finitely presented, locally quasi-finite morphism is scheme-theoretically dense. -/
theorem schemeTheoreticallyDense_preimage_of_flat_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [LocallyQuasiFinite f]
    (W : S.Opens) (hWdense : schemeTheoreticallyDense W) :
    schemeTheoreticallyDense (f ⁻¹ᵁ W) := sorry

end AlgebraicGeometry
