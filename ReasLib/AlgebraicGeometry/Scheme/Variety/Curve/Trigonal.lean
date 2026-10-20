/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Gonality

/-!
# Trigonal curves

Trigonality is the gonality-three condition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- A projective curve is trigonal when its gonality is `3`. -/
def IsTrigonal {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] : Prop :=
  gonality X = 3

/-- Trigonality is equivalent to having gonality `3`. -/
theorem isTrigonal_iff {k : Type u} [Field k] (X : SchemeOverField k)
    [Curve X] [Projective X.hom] :
    IsTrigonal X ↔ gonality X = 3 := sorry

end AlgebraicGeometry.Curve
