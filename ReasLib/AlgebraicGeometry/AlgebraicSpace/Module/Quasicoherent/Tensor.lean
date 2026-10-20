/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The tensor product of quasi-coherent `𝒪_X`-modules is quasi-coherent. -/
instance isQuasicoherent_tensorObj (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent :=
  sorry

/-- An invertible `𝒪_X`-module is quasi-coherent. -/
instance isQuasicoherent_of_isInvertible (L : X.Modules) [isInvertibleObject L] :
    L.IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
