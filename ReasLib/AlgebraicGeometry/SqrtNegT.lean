/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace AlgebraicGeometry.SqrtNegT

/-- The polynomial `X ^ 2 + C X` in `(Polynomial ℂ)[X]`. -/
def definingPolynomial : Polynomial (Polynomial ℂ) :=
  (X : Polynomial (Polynomial ℂ)) ^ 2 + C (X : Polynomial ℂ)

/-- The coordinate ring obtained by adjoining a root of `definingPolynomial`. -/
abbrev coordinateRing : Type :=
  AdjoinRoot definingPolynomial

/-- The affine-line base scheme `Spec (Polynomial ℂ)`. -/
abbrev base : Scheme :=
  Spec (CommRingCat.of (Polynomial ℂ))

/-- The affine scheme with coordinate ring `coordinateRing`. -/
abbrev totalSpace : Scheme :=
  Spec (CommRingCat.of coordinateRing)

/-- The scheme morphism induced by the algebra map from `Polynomial ℂ` to `coordinateRing`. -/
def toBase : totalSpace ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℂ) coordinateRing))

/-- No nonempty open subscheme of `base` admits a section of `toBase`. -/
theorem not_exists_rational_section :
    ¬ ∃ (U : base.Opens), Nonempty U.toScheme ∧
      ∃ σ : U.toScheme ⟶ totalSpace, σ ≫ toBase = U.ι := sorry

end AlgebraicGeometry.SqrtNegT
