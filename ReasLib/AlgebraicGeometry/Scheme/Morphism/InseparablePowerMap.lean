/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Inseparable p-power morphisms

The p-power maps of rational-function fields and polynomial rings give rise to
endomorphisms of their spectra in characteristic `p`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.InseparablePowerMap

/-- The ring homomorphism `𝔽_p(t^p) → 𝔽_p(t)` induced by `u ↦ t ^ p` on
`RatFunc (ZMod p)`. -/
def ratFuncHom (p : ℕ) [Fact p.Prime] : RatFunc (ZMod p) →+* RatFunc (ZMod p) :=
  RatFunc.mapRingHom (Polynomial.expand (ZMod p) p)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.expand_injective (Nat.Prime.pos Fact.out)))

/-- The p-power homomorphism sends `RatFunc.X` to `RatFunc.X ^ p`. -/
theorem ratFuncHom_X (p : ℕ) [Fact p.Prime] :
    ratFuncHom p RatFunc.X = RatFunc.X ^ p := sorry

/-- The spectrum of the rational function field `𝔽_p(t)`, used as both source
and target after identifying `Spec (𝔽_p(t^p))` via `u ↦ t ^ p`. -/
abbrev scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (RatFunc (ZMod p)))

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
