/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.IdealPower.Generation
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.22.3: in Situation 69.22.1, for every p ≥ 0 there exists an integer
c ≥ 0 such that the multiplication map
I^(n-c) ⊗ H^p(X, I^c F) ⟶ H^p(X, I^n F) is surjective for all n ≥ c, and the
image of H^p(X, I^(n+m) F) ⟶ H^p(X, I^n F) is contained in the submodule
I^(m-c) H^p(X, I^n F) for all n ≥ 0, m ≥ c. -/
@[stacks 08AX] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.exists_isGenerationBound :
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
      ∃ c : ℕ,
        AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.IsGenerationBound
          I f F p c)
