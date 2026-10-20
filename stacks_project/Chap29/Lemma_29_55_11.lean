/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Locality
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.55.11: for a scheme whose quasi-compact opens have finitely many irreducible
components, weak normality is equivalent to the ring criterion on every affine open, to the
criterion on one affine open cover, and to the existence of an open cover by weakly normal open
subschemes. -/
@[stacks 0H3U] #check
  (AlgebraicGeometry.Scheme.weaklyNormal_tfae :
    ∀ (X : Scheme.{u})
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X],
      List.TFAE [
        Scheme.WeaklyNormal X,
        ∀ U : X.affineOpens,
          SeminormalRing (Γ(X, (U : X.Opens))) ∧
            ∀ p : ℕ, Nat.Prime p →
              ∀ z w : Γ(X, (U : X.Opens)),
                z ∈ nonZeroDivisors (Γ(X, (U : X.Opens))) →
                z ^ p ∣ w ^ p →
                z ∣ (p : Γ(X, (U : X.Opens))) * w →
                z ∣ w,
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀,
            SeminormalRing (Γ(X, (𝒰.f i).opensRange)) ∧
              ∀ p : ℕ, Nat.Prime p →
                ∀ z w : Γ(X, (𝒰.f i).opensRange),
                  z ∈ nonZeroDivisors (Γ(X, (𝒰.f i).opensRange)) →
                  z ^ p ∣ w ^ p →
                  z ∣ (p : Γ(X, (𝒰.f i).opensRange)) * w →
                  z ∣ w,
        ∃ 𝒰 : X.OpenCover,
          ∀ i : 𝒰.I₀, Scheme.WeaklyNormal ((𝒰.f i).opensRange).toScheme])

#check
  (AlgebraicGeometry.Scheme.weaklyNormal_toScheme :
    ∀ (X : Scheme.{u})
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (hX : Scheme.WeaklyNormal X) (U : X.Opens),
      Scheme.WeaklyNormal U.toScheme)
