/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Coinduction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- Pullback is left adjoint to qcqs pushforward on quasi-coherent modules. -/
abbrev pullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    Scheme.QCoh.pullback f ⊣ Scheme.QCoh.pushforward f :=
  Scheme.QCoh.pullbackPushforwardAdjunction f

end AlgebraicGeometry.GroupoidScheme.QCoh
