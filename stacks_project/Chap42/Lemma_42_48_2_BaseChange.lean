/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_21_1_ProjectiveLineFamily
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveLineFamily.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFamily

#check (AlgebraicGeometry.ProjectiveLineFamily.map :
  ∀ {S : Scheme.{u}} {X X' : Over S} (g : X' ⟶ X), space X' ⟶ space X)

end AlgebraicGeometry.ProjectiveLineFamily
