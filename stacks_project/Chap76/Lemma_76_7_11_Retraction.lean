/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Retractions of morphisms of algebraic spaces over a base

This file records global and étale-local retractions of morphisms of algebraic
spaces that are compatible with a fixed morphism to a base algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X Z : AlgebraicSpace S}

/-- A morphism `i : Z ⟶ X` has a retraction over `B` relative to `f : X ⟶ B` if
some `r : X ⟶ Z` retracts `i` and is compatible with the morphisms to `B`. -/
def HasRetractionOver (i : Z ⟶ X) (f : X ⟶ B) : Prop :=
  ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f

/-- A retraction over a base is equivalently a morphism satisfying the
retraction and base-compatibility equations. -/
theorem hasRetractionOver_iff (i : Z ⟶ X) (f : X ⟶ B) :
    HasRetractionOver i f ↔
      ∃ r : X ⟶ Z, i ≫ r = 𝟙 Z ∧ r ≫ i ≫ f = f :=
  Iff.rfl

/-- A morphism has étale-locally defined retractions over a base if every source
point maps into an étale scheme chart on which the restricted morphism admits a
compatible retraction. -/
def EtaleLocallyHasRetractionOver (i : Z ⟶ X) (f : X ⟶ B) : Prop :=
  ∀ z : Points Z, ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ Points.map i z ∈ Set.range (Points.map φ) ∧
      HasRetractionOver (pullback.snd i φ) (φ ≫ f)

/-- Étale-local retractions over a base are equivalently retractions on étale
scheme charts covering the images of all source points. -/
theorem etaleLocallyHasRetractionOver_iff (i : Z ⟶ X) (f : X ⟶ B) :
    EtaleLocallyHasRetractionOver i f ↔
      ∀ z : Points Z, ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ Points.map i z ∈ Set.range (Points.map φ) ∧
          HasRetractionOver (pullback.snd i φ) (φ ≫ f) :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Hom
