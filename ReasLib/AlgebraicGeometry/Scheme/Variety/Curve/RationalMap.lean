/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- Every rational map over a field from a normal curve to a proper variety is induced by a
unique morphism over that field. -/
theorem existsUnique_hom_of_rationalMap
    {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X] (hX : X.left.isNormal)
    [Variety Y] [IsProper Y.hom] (φ : X.left ⤏ Y.left)
    [φ.IsOver (Spec (CommRingCat.of k))] :
    ∃! f : X ⟶ Y, f.left.toRationalMap = φ := sorry

end AlgebraicGeometry.Curve
