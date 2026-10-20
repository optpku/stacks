/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.Groupoids.Hom.Immersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)
