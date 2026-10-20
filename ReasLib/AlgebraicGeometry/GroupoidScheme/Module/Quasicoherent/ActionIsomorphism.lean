/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

/-- The action morphism of an equivariant quasi-coherent module on a groupoid scheme is
an isomorphism. -/
theorem action_isIso {S : Scheme.{u}} {G : GroupoidScheme S} (A : G.QCoh) :
    IsIso A.action := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
