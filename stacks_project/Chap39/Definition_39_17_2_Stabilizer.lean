/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap39.Lemma_39_13_4_Groupoid
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# Stabilizers of groupoid schemes

This module preserves the source-facing compatibility name for the canonical stabilizer.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

/-- The stabilizer of a groupoid scheme as a bundled group object over its object scheme. -/
noncomputable abbrev stabilizer {S : Scheme.{u}} (G : Groupoid S) : Grp (Over G.U) :=
  AlgebraicGeometry.GroupoidScheme.stabilizer G

end AlgebraicGeometry.Scheme.Groupoid
