/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.RatFunc.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Regular.RationalFunctionCounterexample

/-!
# The p-power morphism of `𝔽_p(t)` and `𝔽_p[t]`

This file constructs the scheme morphisms corresponding to `𝔽_p(t^p) → 𝔽_p(t)`
and `𝔽_p[t^p] → 𝔽_p[t]`, realized by `Polynomial.expand` and its lift to
rational functions.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RationalFunctionRegularityCounterexample

namespace AlgebraicGeometry.InseparablePowerMap

/-- The ring homomorphism `𝔽_p(t^p) → 𝔽_p(t)` induced by `u ↦ t ^ p` on
`BaseField p`. -/
def ratFuncHom (p : ℕ) [Fact p.Prime] : BaseField p →+* BaseField p :=
  RatFunc.mapRingHom (Polynomial.expand (ZMod p) p)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.expand_injective (Nat.Prime.pos Fact.out)))

/-- The p-power homomorphism sends `RatFunc.X` to `RatFunc.X ^ p`. -/
theorem ratFuncHom_X (p : ℕ) [Fact p.Prime] :
    ratFuncHom p RatFunc.X = RatFunc.X ^ p := sorry

/-- The spectrum of the rational function field `𝔽_p(t)`, used as both source
and target after identifying `Spec (𝔽_p(t^p))` via `u ↦ t ^ p`. -/
abbrev scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (BaseField p))

/-- The morphism `Spec (𝔽_p(t)) ⟶ Spec (𝔽_p(t^p))` corresponding to
`ratFuncHom p`. -/
def hom (p : ℕ) [Fact p.Prime] : scheme p ⟶ scheme p :=
  Spec.map (CommRingCat.ofHom (ratFuncHom p))

/-- The affine line `Spec (𝔽_p[t])`. -/
abbrev affineLine (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (Polynomial (ZMod p)))

/-- The morphism corresponding to `𝔽_p[t^p] → 𝔽_p[t]` induced by
`Polynomial.expand`. -/
def affineLineHom (p : ℕ) [Fact p.Prime] : affineLine p ⟶ affineLine p :=
  Spec.map (CommRingCat.ofHom (Polynomial.expand (ZMod p) p).toRingHom)

end AlgebraicGeometry.InseparablePowerMap
