/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# The pullback-pushforward adjunction for quasi-coherent modules

This module restricts the usual module-sheaf pullback-pushforward adjunction to
quasi-coherent modules along a quasi-compact and quasi-separated scheme morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

namespace pullback

/-- Pullback of module sheaves carries quasi-coherent modules to quasi-coherent modules. -/
theorem mapsTo {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.quasiCoherentModuleProperty X ≤
      (Scheme.quasiCoherentModuleProperty Y).inverseImage (Scheme.Modules.pullback f) := sorry

end pullback

/-- Pullback is left adjoint to qcqs pushforward on quasi-coherent modules. -/
noncomputable def pullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    pullback f ⊣ pushforward f :=
  ObjectProperty.FullSubcategory.adjunction
    (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (pullback.mapsTo f) (pushforward.mapsTo f)

end AlgebraicGeometry.Scheme.QCoh
