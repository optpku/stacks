/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap39.Lemma_39_13_4_Groupoid
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer

/-!
# Stabilizer groups of groupoid schemes

This module preserves the source-facing spelling for the canonical stabilizer group.
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

/-- The stabilizer of a groupoid scheme as a bundled group object over its object scheme. -/
noncomputable abbrev stabilizerGroup {S : Scheme.{u}} (G : Groupoid S) :
    CategoryTheory.Grp (CategoryTheory.Over G.U) :=
  AlgebraicGeometry.GroupoidScheme.stabilizer G

/-- Multiplication on the stabilizer induced by groupoid composition. -/
noncomputable abbrev stabilizerMul {S : Scheme.{u}} (G : Groupoid S) :
    G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer ⟶
      G.toPreRelation.stabilizer :=
  AlgebraicGeometry.GroupoidScheme.stabilizerMul G

/-- The unit of the stabilizer induced by the groupoid identity. -/
noncomputable abbrev stabilizerOne {S : Scheme.{u}} (G : Groupoid S) :
    𝟙_ (CategoryTheory.Over G.U) ⟶ G.toPreRelation.stabilizer :=
  AlgebraicGeometry.GroupoidScheme.stabilizerOne G

/-- Inversion on the stabilizer induced by groupoid inversion. -/
noncomputable abbrev stabilizerInv {S : Scheme.{u}} (G : Groupoid S) :
    G.toPreRelation.stabilizer ⟶ G.toPreRelation.stabilizer :=
  AlgebraicGeometry.GroupoidScheme.stabilizerInv G

end AlgebraicGeometry.Scheme.Groupoid
