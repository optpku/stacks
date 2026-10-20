/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Injective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Exercise 111.42.2: injective abelian sheaves are flasque, so their restriction maps are
surjective. This is the property that makes the two-open difference map surjective in the
construction of the Mayer–Vietoris long exact sequence. -/
@[stacks 0D8R] #check
  (TopCat.Sheaf.restriction_surjective_of_injective :
    ∀ {X : TopCat.{u}} (I : X.Sheaf AddCommGrpCat.{u}) [Injective I]
      {U V : Opens X} (hVU : V ≤ U),
      Function.Surjective (I.presheaf.map (homOfLE hVU).op))
