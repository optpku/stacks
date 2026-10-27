/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Restriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Restriction of a locally quasi-coherent étale module to the small étale site
of a representing algebraic space is quasi-coherent. -/
instance restrictModules_isQuasicoherent
    {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}
    (e : F.toGroupoids ≌ X) (ℱ : etaleModules X) [IsLocallyQuasiCoherent ℱ] :
    ((restrictModules e).obj ℱ).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.GroupoidsOver
