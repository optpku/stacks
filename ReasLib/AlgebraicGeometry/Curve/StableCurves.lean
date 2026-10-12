/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.AlgebraicGeometry.Curve.Family
public import ReasLib.AlgebraicGeometry.Curve.StableOfGenus

/-!
# Stable curve families as object properties

This file records the object properties of scheme families of curves whose
residue-field fibres are stable curves, and of those families of a given genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves whose residue-field fibres are
stable curves. -/
def stableCurves (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P => ∀ s : P.base.left, isStableCurve (Over.mk (P.hom.fiberToSpecResidueField s))

/-- Membership in `stableCurves` is that every residue-field fibre is a stable
curve. -/
theorem stableCurves_iff {S : Scheme.{u}} (P : Obj S) :
    stableCurves S P ↔
      ∀ s : P.base.left, isStableCurve (Over.mk (P.hom.fiberToSpecResidueField s)) :=
  Iff.rfl

/-- The object property of families of curves that are stable of genus `g`. -/
def stableCurvesOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P => IsStableFamilyOfGenus g P.hom

/-- Membership in `stableCurvesOfGenus g` is that the structure morphism is a
stable family of genus `g`. -/
theorem stableCurvesOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableCurvesOfGenus g S P ↔ IsStableFamilyOfGenus g P.hom :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
