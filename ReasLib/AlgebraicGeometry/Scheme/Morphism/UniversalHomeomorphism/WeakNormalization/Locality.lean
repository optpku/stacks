/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Open
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Affine
public import Mathlib.Data.List.TFAE

/-!
# Locality of weak normality

This module gives affine and open-cover criteria for weak normality and records preservation under
restriction to open subschemes.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]

/-- Every open subscheme of a weakly normal scheme is weakly normal. -/
theorem weaklyNormal_toScheme (hX : WeaklyNormal X) (U : X.Opens) :
    WeaklyNormal U.toScheme := sorry

/-- Weak normality is inherited canonically by open subschemes. -/
instance instWeaklyNormalToScheme {X : Scheme.{u}}
    [HasFiniteIrreducibleComponentsOnCompactOpens X] [WeaklyNormal X] (U : X.Opens) :
    WeaklyNormal U.toScheme :=
  weaklyNormal_toScheme X inferInstance U

/-- A scheme is weakly normal exactly when it has an open cover by weakly normal open
subschemes. -/
theorem weaklyNormal_iff_exists_openCover :
    WeaklyNormal X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, WeaklyNormal ((𝒰.f i).opensRange).toScheme := sorry

/-- A scheme is weakly normal exactly when every affine open has a seminormal section ring
satisfying prime divisibility by nonzerodivisors. -/
theorem weaklyNormal_iff_forall_affineOpen_sectionsRing_primeDivisibility :
    WeaklyNormal X ↔
      ∀ U : X.affineOpens,
        SeminormalRing (Γ(X, (U : X.Opens))) ∧
          ∀ p : ℕ, Nat.Prime p →
            ∀ z w : Γ(X, (U : X.Opens)),
              z ∈ nonZeroDivisors (Γ(X, (U : X.Opens))) →
              z ^ p ∣ w ^ p →
              z ∣ (p : Γ(X, (U : X.Opens))) * w →
              z ∣ w := sorry

/-- A scheme is weakly normal exactly when it has an affine open cover whose section rings are
seminormal and satisfy prime divisibility by nonzerodivisors. -/
theorem weaklyNormal_iff_exists_affineOpenCover_sectionsRing_primeDivisibility :
    WeaklyNormal X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          SeminormalRing (Γ(X, (𝒰.f i).opensRange)) ∧
            ∀ p : ℕ, Nat.Prime p →
              ∀ z w : Γ(X, (𝒰.f i).opensRange),
                z ∈ nonZeroDivisors (Γ(X, (𝒰.f i).opensRange)) →
                z ^ p ∣ w ^ p →
                z ∣ (p : Γ(X, (𝒰.f i).opensRange)) * w →
                z ∣ w := sorry

/-- Weak normality, its affine section-ring criteria, and the existence of a weakly normal open
cover are equivalent. -/
theorem weaklyNormal_tfae :
    List.TFAE [
      WeaklyNormal X,
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
        ∀ i : 𝒰.I₀, WeaklyNormal ((𝒰.f i).opensRange).toScheme] := sorry

end AlgebraicGeometry.Scheme
