/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Quotient
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.4 (1): in Situation 69.22.1, for every p ≥ 0 there exists c₁ ≥ 0
such that for all n ≥ c₁ the kernel of H^p(X, F) ⟶ H^p(X, F / I^n F) is contained
in I^(n-c₁) H^p(X, F). -/
@[stacks 08AY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.exists_ker_le_pow :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A]
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules]
      (p : ℕ),
      ∃ c : ℕ, ∀ (n : ℕ), c ≤ n →
        LinearMap.ker
            (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toQuotientCohomology
              I f F p n).hom ≤
          Ideal.PowerSubmodule.stage I
            (AlgebraicGeometry.AlgebraicSpace.Modules.GradedCohomology.cohomologyOver
              (𝟙 (Spec (CommRingCat.of A))) f F p)
            (n - c))

/- Lemma 69.22.4 (2): in Situation 69.22.1, the inverse system
(H^p(X, F / I^n F))_{n ∈ ℕ} satisfies the Mittag-Leffler condition. -/
@[stacks 08AY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.isMittagLeffler_quotientSystem :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A]
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules]
      (p : ℕ),
      SequentialInverseSystem.IsMittagLeffler
        (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem
          I f F p))

/- Lemma 69.22.4 (3): in Situation 69.22.1, for every p and n there exists
c₂(n) ≥ n such that for all k ≥ c₂(n) the image of
H^p(X, F / I^k F) ⟶ H^p(X, F / I^n F) equals the image of
H^p(X, F) ⟶ H^p(X, F / I^n F). -/
@[stacks 08AY] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.exists_range_eq_toQuotient :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A]
      (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules]
      (p : ℕ),
      ∀ n : ℕ, ∃ (c : ℕ) (hc : n ≤ c),
        ∀ (k : ℕ) (hk : c ≤ k),
          LinearMap.range
              ((AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem
                I f F p).transitionMap (hc.trans hk)).hom =
            LinearMap.range
              (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.toQuotientCohomology
                I f F p n).hom)
