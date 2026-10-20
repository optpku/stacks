/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal

@[expose] public section
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived
variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [ModuleDerived.KFlat.HomotopyTensorDescends X]
variable [ModuleDerived.KFlat.HomotopyTensorDescends Y]
variable [ModuleDerived.KFlat.TensorDescends X] [ModuleDerived.KFlat.TensorDescends Y]
variable [ModuleDerived.KFlat.IsLocalization X] [ModuleDerived.KFlat.IsLocalization Y]

/-- The ringed-space derived pullback inherits its canonical monoidal core
from the opens-site good-flat-model localization of the same pullback. -/
@[implicit_reducible]
def opensSiteMonoidal : (modulePullbackDerived f).Monoidal :=
  -- Local instance justification (defeq pin): use the named good-flat-model localization theorem for the source opens site, without selecting a new tensor model.
  letI := RingedSite.Hom.ModuleDerived.KFlat.TermwiseFlat.localizationIsLocalization Y.sheaf
  -- Local instance justification (defeq pin): invert the specified homotopy tensor comparison of the actual opens-site pullback.
  letI := RingedSite.Hom.modulePullbackHomotopy.TensorComparison.isInvertible (opensRingedSiteHom f)
  -- Local instance justification (defeq pin): invert the specified total-left-derived counit on good flat models.
  letI := RingedSite.Hom.modulePullbackDerived.GoodModels.comparison_isIso (opensRingedSiteHom f)
  RingedSite.Hom.modulePullbackDerived.monoidal (opensRingedSiteHom f)

end AlgebraicGeometry.RingedSpace.modulePullbackDerived
