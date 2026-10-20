/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap79.«79_12_0_1_FinitePart»
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.SectionPair

/-!
# Finite-part pairs containing a section graph

A variant of a finite-part pair `(a, Z)` for a morphism `f : X ⟶ Y` of algebraic
spaces over a scheme `S` together with a section `σ : Y ⟶ X` of `f`: the graph
`(1_T, σ ∘ a) : T ⟶ T ×_Y X` factors through the open subspace `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.sectionGraph_condition :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → 𝟙 T ≫ a = (a ≫ σ) ≫ f)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.sectionGraph :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → (T ⟶ pullback a f))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.sectionGraph_fst :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    FinitePart.sectionGraph a f σ hσ ≫ pullback.fst a f = 𝟙 T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.sectionGraph_snd :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (a : T ⟶ Y) (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y),
    FinitePart.sectionGraph a f σ hσ ≫ pullback.snd a f = a ≫ σ)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → AlgebraicSpace S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.of :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} {σ : Y ⟶ X}
    (hσ : σ ≫ f = 𝟙 Y) (p : FinitePart f T),
    (∃ ℓ : T ⟶ p.Z.X, ℓ ≫ p.Z.ι = FinitePart.sectionGraph p.a f σ hσ) →
      FinitePart.WithSection f σ hσ T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.spec :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} (p : FinitePart.WithSection f σ hσ T),
    IsOpenImmersion p.Z.ι ∧ IsFinite p.pr ∧
      ∃ ℓ : T ⟶ p.Z.X, ℓ ≫ p.Z.ι = FinitePart.sectionGraph p.a f σ hσ)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.lift :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y} {σ : Y ⟶ X}
    {hσ : σ ≫ f = 𝟙 Y} (p : FinitePart.WithSection f σ hσ T), T ⟶ p.Z.X)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.lift_comp :
  ∀ {S : Scheme.{u}} {X Y T : AlgebraicSpace S} {f : X ⟶ Y}
    {σ : Y ⟶ X} {hσ : σ ≫ f = 𝟙 Y} (p : FinitePart.WithSection f σ hσ T),
    p.lift ≫ p.Z.ι = FinitePart.sectionGraph p.a f σ hσ)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection.over :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X),
    σ ≫ f = 𝟙 Y → Over S → Type (u + 1))
