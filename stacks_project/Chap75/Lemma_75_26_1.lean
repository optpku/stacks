module

import StacksCheckRecall
public import stacks_project.Chap75.Lemma_75_26_1_FiberBetti

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

/- Lemma 75.26.1 (1): formation of the degreewise fiber Betti function of a
pseudo-coherent (for example perfect) derived module commutes with arbitrary base change. -/
@[stacks 0D1Y] #check
  (ModuleDerived.fiberBetti_pullback :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (f : Y ⟶ X) → (E : ModuleDerived X) → IsPseudoCoherent X E → (i : ℤ) →
      ModuleDerived.fiberBetti ((ModuleDerived.pullback f).obj E) i =
        fun y ↦ ModuleDerived.fiberBetti E i (Points.map f y))

/- Lemma 75.26.1 (2): every degreewise fiber Betti function of a pseudo-coherent
(for example perfect) derived module is upper semicontinuous. -/
@[stacks 0D1Y] #check
  (ModuleDerived.fiberBetti_upperSemicontinuous :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (E : ModuleDerived X) →
      IsPseudoCoherent X E → (i : ℤ) →
      UpperSemicontinuous (ModuleDerived.fiberBetti E i))

/- Lemma 75.26.1 (3): every level set of a degreewise fiber Betti function of a
pseudo-coherent (for example perfect) derived module is étale locally constructible. -/
@[stacks 0D1Y] #check
  (ModuleDerived.fiberBetti_levelSet_isEtaleLocallyConstructible :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (E : ModuleDerived X) →
      IsPseudoCoherent X E → (i : ℤ) → (n : ℕ) →
      IsEtaleLocallyConstructible ((ModuleDerived.fiberBetti E i) ⁻¹' {n}))
