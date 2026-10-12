/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action
public import stacks_project.Chap39.Lemma_39_13_4_Groupoid

/-!
# Compatibility names for action groupoids

This module preserves the earlier `AlgebraicGeometry.Scheme.Groupoid` spellings for the
canonical action-groupoid construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

/-- Compatibility spelling for the source map of an action groupoid. -/
abbrev actionSource {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :=
  AlgebraicGeometry.GroupoidScheme.actionSource G X

/-- Compatibility spelling for the target map of an action groupoid. -/
abbrev actionTarget {B : Scheme.{u}} (G : Grp (Over B)) (X : GroupScheme.Action G) :=
  AlgebraicGeometry.GroupoidScheme.actionTarget G X

/-- Compatibility spelling for the action groupoid over the action's base scheme. -/
abbrev ofAction {B : Scheme.{u}} (G : Grp (Over B))
    (X : GroupScheme.Action G) : Groupoid B :=
  AlgebraicGeometry.GroupoidScheme.ofAction G X

/-- Compatibility spelling for an action groupoid regarded over an ambient base scheme. -/
abbrev action {S : Scheme.{u}} (Y : Over S) (G : Grp (Over Y.left))
    (X : GroupScheme.Action G) : Groupoid S :=
  AlgebraicGeometry.GroupoidScheme.action Y G X

end AlgebraicGeometry.Scheme.Groupoid
