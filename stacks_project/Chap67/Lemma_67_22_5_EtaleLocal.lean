/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.EtaleLocal
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt

/-!
# Étale scheme squares through a point

The pointwise testing predicates are provided by their reusable mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleSquareAt :
  ∀ {S : Scheme.{u}} (Q : MorphismProperty Scheme.Germ.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : AlgebraicSpace.Points X), Prop)
