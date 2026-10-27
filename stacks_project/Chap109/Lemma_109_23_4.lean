/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableContraction
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

universe u

/- Lemma 109.23.4 (1) -/
@[stacks 0E8A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_contractionToStable :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) {g : ℕ} (hg : 2 ≤ g)
    [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne f)),
    ∃ (Y : AlgebraicSpace S) (q : Y ⟶ ofOver (Over.mk (𝟙 S)))
      (c : X ⟶ Y) (hc : c ≫ q = f), IsContractionToStable c hc)

/- Lemma 109.23.4 (2) -/
@[stacks 0E8A] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.contractionToStable_unique :
    ∀ {S : Scheme.{u}} {X Y₁ Y₂ : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S)))
    (q₁ : Y₁ ⟶ ofOver (Over.mk (𝟙 S))) (q₂ : Y₂ ⟶ ofOver (Over.mk (𝟙 S)))
    {g : ℕ} (hg : 2 ≤ g) [IsFamily f] [Prestable f]
    (hgenus : SheafOfModules.IsFiniteLocallyFreeOfRank g
      (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.higherDirectImageOne f))
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ q₁ = f) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ q₂ = f)
    (h₁ : IsContractionToStable c₁ hc₁) (h₂ : IsContractionToStable c₂ hc₂),
    ∃! e : Y₁ ≅ Y₂, e.hom ≫ q₂ = q₁ ∧ c₁ ≫ e.hom = c₂)
