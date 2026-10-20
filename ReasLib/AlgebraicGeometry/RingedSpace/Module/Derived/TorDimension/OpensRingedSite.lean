/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Infer the existing canonical tensor model for this commutative presentation.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

/-!
# Tor-amplitude and the opens ringed site

This leaf compares the intrinsic Tor-amplitude predicate on a ringed space with its shared
ringed-site presentation.  Consumers of the intrinsic predicate need not import the bundled
opens-site infrastructure.
-/

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [CategoryTheory.DerivedCategory.DerivedTensor.Right.Has (C := Modules X)]

/-- Tor-amplitude on a ringed space agrees with the shared ringed-site predicate on its
canonical opens ringed site. -/
@[stacks 08CG "opens-ringed-site comparison"]
theorem hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn
    (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn
        (O := X.sheaf) E a b := sorry

end AlgebraicGeometry.RingedSpace
