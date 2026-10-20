/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints

/-!
# Étale-chart and geometric-stalk association predicates

Typed source-facing checks of the canonical module API.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleWeakAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.forallEtaleWeakAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.etaleStalkWeakAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.existsEtaleAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.forallEtaleAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.etaleStalkAss :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, X.Modules → Points X → Prop)
