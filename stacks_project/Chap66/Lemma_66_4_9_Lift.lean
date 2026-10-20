/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization

/-!
# Factorization through open immersions of algebraic spaces

A morphism of algebraic spaces factors through an open immersion if and only if the
induced map on points lands in the image of that immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.exists_lift_iff_range_subset :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ i = f) ↔ Set.range (Points.map f) ⊆ Set.range (Points.map i))

#check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.existsUnique_lift_iff_range_subset :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ X) [IsOpenImmersion i] (f : Y ⟶ X),
    (∃! g : Y ⟶ Z, g ≫ i = f) ↔ Set.range (Points.map f) ⊆ Set.range (Points.map i))

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.exists_lift_iff_range_subset :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (X' : OpenSubspace X) (f : Y ⟶ X),
    (∃ g : Y ⟶ X'.X, g ≫ X'.ι = f) ↔ Set.range (Points.map f) ⊆ X'.pointsSet)
