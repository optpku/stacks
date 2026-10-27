/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map

/-!
# Relative flatness of quasi-coherent modules via étale stalks

A quasi-coherent module on an algebraic space is flat at a point over the target if and only if
its étale stalk at a geometric point over that point is flat along the induced map of étale
local rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A quasi-coherent module is relatively flat at a point if and only if its étale stalk at
any specified geometric point lying over that point is flat along the induced map of étale
local rings. -/
@[stacks 05VU]
theorem flatOverAt_iff_stalk_flatAlong (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y)
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) :
    flatOverAt F f x ↔
      Module.FlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F) :=
  sorry

/-- Relative flatness at the image of a geometric point is equivalent to flatness of the étale
stalk along the induced étale local ring map. -/
theorem flatOverAt_iff_stalk_flatAlong_image (F : X.Modules) [F.IsQuasicoherent]
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    flatOverAt F f xbar.image ↔
      Module.FlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
