/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A section of an invertible module on a locally Noetherian scheme is regular exactly when it
is nonvanishing at every associated point of the scheme. -/
theorem isRegularSection_iff_associatedPoints_subset_sectionNonvanishingLocus
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) :
    RingedSpace.IsRegularSection ℒ s ↔
      X.associatedPoints ⊆ RingedSpace.sectionNonvanishingLocus X.toRingedSpace ℒ s := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible
