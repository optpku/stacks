/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Normal

@[expose] public section

/-!
# Normalization prerequisites for locally Noetherian schemes

This leaf records the generic-point normalization prerequisites supplied by a
locally Noetherian scheme.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

/-- The generic-point residue-field coproduct of a locally Noetherian scheme is quasi-compact. -/
instance instGenericPointsQuasiCompact (X : Scheme.{u}) [IsLocallyNoetherian X] :
    QuasiCompact (genericPointSpectrumCoproductTo X) := sorry

/-- The generic-point residue-field coproduct of a locally Noetherian scheme is quasi-separated. -/
instance instGenericPointsQuasiSeparated (X : Scheme.{u}) [IsLocallyNoetherian X] :
    QuasiSeparated (genericPointSpectrumCoproductTo X) := sorry

/-- Reduction preserves local Noetherianity. -/
instance instReduction (X : Scheme.{u}) [IsLocallyNoetherian X] :
    IsLocallyNoetherian X.nilradical.subscheme := sorry

end AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian

namespace AlgebraicGeometry.Scheme

/-- The canonical normalization scheme of a Noetherian scheme. -/
noncomputable abbrev normalizationOfIsNoetherian (Y : Scheme.{u}) [hY : IsNoetherian Y] :
    Scheme.{u} :=
  @normalization Y
    (@Normalization.LocallyNoetherian.instGenericPointsQuasiCompact Y
      hY.toIsLocallyNoetherian)
    (@Normalization.LocallyNoetherian.instGenericPointsQuasiSeparated Y
      hY.toIsLocallyNoetherian)

/-- The canonical normalization morphism of a Noetherian scheme. -/
noncomputable abbrev normalizationToOfIsNoetherian (Y : Scheme.{u}) [hY : IsNoetherian Y] :=
  @normalizationTo Y
    (@Normalization.LocallyNoetherian.instGenericPointsQuasiCompact Y
      hY.toIsLocallyNoetherian)
    (@Normalization.LocallyNoetherian.instGenericPointsQuasiSeparated Y
      hY.toIsLocallyNoetherian)

end AlgebraicGeometry.Scheme
