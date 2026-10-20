/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

/-!
# Brill–Noether data for curves

The Brill–Noether number and the associated existence criterion for linear series.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- The integer Brill–Noether number is `g - (r + 1) * (g - d + r)`. -/
def brillNoetherNumber (g r d : ℕ) : ℤ :=
  (g : ℤ) - ((r : ℤ) + 1) * ((g : ℤ) - (d : ℤ) + (r : ℤ))

/-- The Brill–Noether number has its defining integer expression. -/
theorem brillNoetherNumber_def (g r d : ℕ) :
    brillNoetherNumber g r d =
      (g : ℤ) - ((r : ℤ) + 1) * ((g : ℤ) - (d : ℤ) + (r : ℤ)) := sorry

/-- A smooth projective geometrically irreducible curve is Brill–Noether-general
when linear-series existence is equivalent to nonnegativity of its Brill–Noether number. -/
def IsBrillNoetherGeneral {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    Prop :=
  ∀ d r : ℕ,
    Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
      0 ≤ brillNoetherNumber (genus X) r d

/-- Brill–Noether-generality is exactly the stated linear-series existence criterion. -/
theorem isBrillNoetherGeneral_iff {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom] :
    IsBrillNoetherGeneral X ↔
      ∀ d r : ℕ,
        Nonempty (LinearSeries X topologicalKrullDim_eq_one.le d r) ↔
          0 ≤ brillNoetherNumber (genus X) r d := sorry

end AlgebraicGeometry.Curve
