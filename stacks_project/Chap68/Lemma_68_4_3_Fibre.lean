/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre

/-!
# Finite self-relation fibres over a point of an algebraic space

A point of an algebraic space has a finite self-relation fibre when an étale
morphism from a scheme has finite fibre of `|R| → |U| ×_{|X|} |U|` over a pair of
points mapping to it. This module records that pointwise condition, the matching
universal étale-chart test, and the equivalent field-valued-point formulations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Finiteness of an étale-chart self-relation fibre characterizes the existence
of a monomorphic field-valued representative. -/
#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleRelationFiniteFibre_iff_existsMonoFieldValuedPoint :
  ∀ {S : Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    AlgebraicGeometry.AlgebraicSpace.existsEtaleRelationFiniteFibre X x ↔
      AlgebraicGeometry.AlgebraicSpace.existsMonoFieldValuedPoint X x)
