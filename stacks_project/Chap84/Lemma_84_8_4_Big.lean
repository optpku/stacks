/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos

/-! # Compatibility check for the canonical big étale morphism of topoi -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Etale.Big.morphismOfTopoi :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (Y ⟶ X) → MorphismOfTopoiIn (overEtaleTopology X) (overEtaleTopology Y))
