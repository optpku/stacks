/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap75.Lemma_75_26_2_FiberFinrank

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

/- Lemma 75.26.2 (1): formation of the fiber cohomology finrank function commutes
with arbitrary cartesian base change. -/
@[stacks 0E0R] #check
  (fiberCohomologyFinrank_baseChange :
    {Y : Scheme.{u}} → {X X' : AlgebraicSpace Y} → {T : Over Y} →
      (g' : X' ⟶ X) → (f' : X' ⟶ ofOver T) →
      (f : X ⟶ ofOver (Over.mk (𝟙 Y))) → (g : ofOver T ⟶ ofOver (Over.mk (𝟙 Y))) →
      [Flat f] → [Proper f] → [FinitePresentation f] →
      (ℱ : X.Modules) → [ℱ.IsFinitePresentation] →
      (hℱ_flat : Modules.flatOver ℱ f) → (sq : IsPullback g' f' f g) → (i : ℤ) →
      fiberCohomologyFinrank f' ((Modules.pullback g').obj ℱ) i =
        fun t ↦ fiberCohomologyFinrank f ℱ i (T.hom t))

/- Lemma 75.26.2 (2): every fiber cohomology finrank function is upper
semicontinuous. -/
@[stacks 0E0R] #check
  (fiberCohomologyFinrank_upperSemicontinuous :
    {Y : Scheme.{u}} → {X : AlgebraicSpace Y} →
      (f : X ⟶ ofOver (Over.mk (𝟙 Y))) →
      [Flat f] → [Proper f] → [FinitePresentation f] →
      (ℱ : X.Modules) → [ℱ.IsFinitePresentation] →
      (hℱ_flat : Modules.flatOver ℱ f) → (i : ℤ) →
      UpperSemicontinuous (fiberCohomologyFinrank f ℱ i))

/- Lemma 75.26.2 (3): every level set of a fiber cohomology finrank function is
locally constructible in `Y`. -/
@[stacks 0E0R] #check
  (fiberCohomologyFinrank_levelSet_isLocallyConstructible :
    {Y : Scheme.{u}} → {X : AlgebraicSpace Y} →
      (f : X ⟶ ofOver (Over.mk (𝟙 Y))) →
      [Flat f] → [Proper f] → [FinitePresentation f] →
      (ℱ : X.Modules) → [ℱ.IsFinitePresentation] →
      (hℱ_flat : Modules.flatOver ℱ f) → (i : ℤ) → (n : ℕ) →
      Topology.IsLocallyConstructible ((fiberCohomologyFinrank f ℱ i) ⁻¹' {n}))
