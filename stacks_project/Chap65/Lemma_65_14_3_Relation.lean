/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PreRelation

universe u

#check (AlgebraicGeometry.Scheme.PreRelation.instIsEtaleEquivalenceRelation_ofAut :
  ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G] (ρ : G →* Aut U)
    [IsResidueFieldFree ρ], (ofAut ρ).IsEtaleEquivalenceRelation)
