/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Diagram
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

/-!
# Compatibility names for the stabilizer diagram

This module preserves source-facing spellings used by existing chapter files.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

/-- Compatibility spelling for the structure morphism of the canonical stabilizer. -/
noncomputable abbrev stabilizerMap {S : Scheme.{u}} (G : Groupoid S) :
    G.stabilizer.X.left ⟶ G.U :=
  AlgebraicGeometry.GroupoidScheme.stabilizerMap G

/-- Compatibility spelling for the groupoid identity section into the stabilizer. -/
noncomputable abbrev unitSection {S : Scheme.{u}} (G : Groupoid S) :
    G.U ⟶ G.stabilizer.X.left :=
  AlgebraicGeometry.GroupoidScheme.stabilizerOneLift G

end AlgebraicGeometry.Scheme.Groupoid
