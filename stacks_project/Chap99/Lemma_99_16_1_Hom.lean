/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.HomFunctor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped DerivedExt

noncomputable section

universe u

/- Derived base-change compatibility API. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.baseChangeHom :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K E : ModuleDerived X) {V V' : AlgebraicSpace S}
    {g : V ⟶ Y} {g' : V' ⟶ Y} (φ : V' ⟶ V) (hφ : φ ≫ g = g'),
    (baseChangePullback f g K ⟶ baseChangePullback f g E) →
      (baseChangePullback f g' K ⟶ baseChangePullback f g' E))
