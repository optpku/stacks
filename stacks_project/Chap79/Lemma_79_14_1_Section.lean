/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap79.«79_12_0_2_FinitePart»

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Opposite

universe u

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.Point :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → Over S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionFunctor :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → (Over S)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.withSectionToY :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Separated f] [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    FinitePart.withSectionSpace f σ hσ ⟶ Y)
