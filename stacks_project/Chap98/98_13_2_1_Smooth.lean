/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_3_1
public import stacks_project.Chap98.«98_3_1_1_Functor»
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations

/-!
# Smoothness on associated predeformation categories

A 1-morphism of categories fibred in groupoids over a locally Noetherian scheme
is smooth on predeformations when every induced map of predeformation categories
at a finite-type field is a smooth morphism over `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S},
    (X ⟶ Y) → Prop)
