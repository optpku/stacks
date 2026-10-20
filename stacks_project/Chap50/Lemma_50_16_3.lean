/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter.ExceptionalTwist
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.16.3: for a blowup `π` of the affine coordinate center, with exceptional divisor
`E = π.exceptionalDivisor`, the canonical map from a locally free module `𝓔[0]` to the derived
pushforward of `(π^*𝓔 ⊗ 𝒪(iE))[0]` is an isomorphism for `i : Fin n`, i.e. for
`0 ≤ i ≤ n - 1`. -/
@[stacks 0G5H] #check (AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalTwistComparison_isIso :
    ∀ (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (𝓔 : (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))).Modules)
    [𝓔.IsLocallyFree] (i : Fin n),
    IsIso (π.exceptionalTwistComparison 𝓔 i))
