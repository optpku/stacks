/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DeRham.AffineLine

@[expose] public section

universe u

/- Example 50.10.6 (1): under the canonical identification of the Kähler differentials of
`Polynomial k` with `Polynomial k`, the differential of `X ^ n` is
`C (n : k) * X ^ (n - 1)`. -/
@[stacks 0FUJ]
#check (KaehlerDifferential.polynomialEquiv_D_X_pow :
  ∀ (k : Type u) [Field k] (n : ℕ),
    KaehlerDifferential.polynomialEquiv k
        (KaehlerDifferential.D k (Polynomial k) (Polynomial.X ^ n)) =
      Polynomial.C (n : k) * Polynomial.X ^ (n - 1))

/- Example 50.10.6 (2): in positive characteristic, the degree-zero de Rham cohomology of
the affine line over `k` is not finite-dimensional over `k`. -/
@[stacks 0FUJ]
#check (AlgebraicGeometry.Scheme.DeRham.affineLineH0_not_finite :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p],
    ¬ Module.Finite k
      (AlgebraicGeometry.Scheme.DeRham.affineCohomology
        (CommRingCat.ofHom (algebraMap k (Polynomial k))) 0))

/- Example 50.10.6 (3): in positive characteristic, the degree-one de Rham cohomology of
the affine line over `k` is not finite-dimensional over `k`. -/
@[stacks 0FUJ]
#check (AlgebraicGeometry.Scheme.DeRham.affineLineH1_not_finite :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p],
    ¬ Module.Finite k
      (AlgebraicGeometry.Scheme.DeRham.affineCohomology
        (CommRingCat.ofHom (algebraMap k (Polynomial k))) 1))
