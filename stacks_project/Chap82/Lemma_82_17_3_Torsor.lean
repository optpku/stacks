/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Pullback of an invertible module to its multiplicative torsor is invertible. -/
abbrev instIsInvertibleObject_pullback_gmTorsorπ (L : X.Modules)
    [isInvertibleObject L] : isInvertibleObject ((pullback (gmTorsorπ L)).obj L) :=
  isInvertibleObject_pullback (gmTorsorπ L) L

/- The multiplicative torsor and its tautological trivialization. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsor :
  (L : X.Modules) → [isInvertibleObject L] → AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorπ :
  (L : X.Modules) → [isInvertibleObject L] → gmTorsor L ⟶ X)
#check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorTriv :
  (L : X.Modules) → [isInvertibleObject L] →
    (pullback (gmTorsorπ L)).obj L ≅ 𝟙_ (gmTorsor L).Modules)

end AlgebraicGeometry.AlgebraicSpace.Modules
