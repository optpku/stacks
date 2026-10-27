/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Extension

/-! # Extension commutes with pullback along a morphism of represented schemes -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} {T Z : Over S}

/-- Inverse images commute with extension, by uniqueness of their actual adjunctions. -/
def extensionPullbackIso (t : T ⟶ Z) :
    Scheme.Modules.pullback t.left ⋙ extension T ≅
      extension Z ⋙ Modules.pullback (ofOverMap t) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction t.left).comp
      (extensionAdjunction T)).leftAdjointUniq
    (((extensionAdjunction Z).comp
      (Modules.pullbackPushforwardAdjunction (ofOverMap t))).ofNatIsoRight
        (pushforwardComparisonIso t))


end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
