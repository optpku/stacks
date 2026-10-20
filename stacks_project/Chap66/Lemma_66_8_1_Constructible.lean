/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Topology

universe u

#check (AlgebraicGeometry.AlgebraicSpace.schemePreimage :
    ∀ {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S},
      (ofOver U ⟶ X) → Set (Points X) → Set U.left)

#check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, Set (Points X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible.ofOver_iff :
    ∀ {S : Scheme.{u}} {T : Over S} (E : Set (Points (ofOver T))),
      IsEtaleLocallyConstructible E ↔ IsLocallyConstructible (ofOver.pointsEquiv T ⁻¹' E))
