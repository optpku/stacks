/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Affine
import StacksCheckRecall

universe u

/- Lemma 36.38.3 (1): for an affine scheme `Spec R`, the group `K₀(Spec R)` is
additively equivalent to the projective-module group `K₀(R)`. -/
@[stacks 0FDH] #check
  (AlgebraicGeometry.Scheme.K0.exists_affineEquiv :
    ∀ R : CommRingCat.{u},
      Nonempty
        (AlgebraicGeometry.Scheme.K0 (AlgebraicGeometry.Spec R) ≃+
          CategoryTheory.ModuleCat.K0.projective R))

/- Lemma 36.38.3 (2): if `R` is Noetherian, the group `K₀'(Spec R)` is
additively equivalent to the finite-module group `K₀'(R)`. -/
@[stacks 0FDH] #check
  (AlgebraicGeometry.Scheme.K0'.affineEquiv :
    ∀ (R : CommRingCat.{u}) [IsNoetherianRing R],
      AlgebraicGeometry.Scheme.K0' (AlgebraicGeometry.Spec R) ≃+
        CategoryTheory.ModuleCat.K0.finite R)
