/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace AlgebraicGeometry.NoQuasiSection

/-- The coordinate ring `ℂ[t]` of the affine line. -/
abbrev BaseRing : Type :=
  Polynomial ℂ

/-- The coordinate ring `ℂ[t][x]` of the affine plane over `ℂ`. -/
abbrev PlaneRing : Type :=
  Polynomial BaseRing

/-- The affine scheme `Spec(ℂ[t])`. -/
abbrev base : Scheme :=
  Spec (CommRingCat.of BaseRing)

/-- The image of `t - α` in `ℂ[t][x]` under the coefficient embedding. -/
def linearFactor (α : ℂ) : PlaneRing :=
  C (X - C α : BaseRing)

/-- The affine scheme `Spec(ℂ[x, t, 1/f])`. -/
def ambient (f : PlaneRing) : Scheme :=
  Spec (CommRingCat.of (Localization.Away f))

/-- The morphism from `ambient f` to `base` induced by coefficient inclusion
and localization away from `f`. -/
def toBase (f : PlaneRing) : ambient f ⟶ base :=
  Spec.map (CommRingCat.ofHom ((algebraMap PlaneRing (Localization.Away f)).comp C))

/-- The existence of a closed subscheme of `ambient f` whose composite with
`toBase f` is finite and surjective. -/
def HasFiniteSurjectiveClosedSubscheme (f : PlaneRing) : Prop :=
  ∃ (Z : Scheme) (i : Z ⟶ ambient f),
    IsClosedImmersion i ∧ IsFinite (i ≫ toBase f) ∧ Surjective (i ≫ toBase f)

/-- The explicit polynomial `(x * t - 2) * (x - t + 3)` in `ℂ[t][x]`. -/
def candidate : PlaneRing :=
  (X * C (X : BaseRing) - C (C (2 : ℂ))) *
    (X - C (X : BaseRing) + C (C (3 : ℂ)))

/-- The explicit polynomial `candidate` is not divisible by any `linearFactor α`. -/
theorem not_dvd_candidate : ∀ α : ℂ, ¬ linearFactor α ∣ candidate := sorry

/-- There is a polynomial with no factor `t - α` whose principal affine open
admits no finite surjective closed subscheme over `Spec(ℂ[t])`. -/
theorem exists_polynomial :
    ∃ f : PlaneRing, (∀ α : ℂ, ¬ linearFactor α ∣ f) ∧
      ¬ HasFiniteSurjectiveClosedSubscheme f := sorry

end AlgebraicGeometry.NoQuasiSection
