/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Comparison
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso

/-!
# Quasi-isomorphisms for enriched cochain homotopy categories

This leaf transports Mathlib's canonical cochain quasi-isomorphisms across the enriched-to-ordinary
homotopy comparison.  Its calculus and saturation facts are reusable without importing the
derived-category comparison itself.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]

/-- Quasi-isomorphisms in the explicit `R`-linear cochain homotopy category are the inverse
image of Mathlib's canonical cochain quasi-isomorphisms. -/
@[stacks 09KX "enriched cochain quasi-isomorphisms over a linear base ring"]
abbrev quasiIso :
    MorphismProperty (DifferentialGradedCategory.K R (CochainComplex A ℤ)) :=
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).inverseImage
    (toMathlib (R := R) (C := A))

/-- Explicit `R`-linear enriched cochain quasi-isomorphisms admit a left calculus of fractions. -/
@[stacks 09KX "left calculus for enriched cochain quasi-isomorphisms over a linear base ring"]
def quasiIsoHasLeftCalculus :
    (quasiIso (R := R) (A := A)).HasLeftCalculusOfFractions := sorry

/-- Explicit `R`-linear enriched cochain quasi-isomorphisms admit a right calculus of fractions. -/
@[stacks 09KX "right calculus for enriched cochain quasi-isomorphisms over a linear base ring"]
def quasiIsoHasRightCalculus :
    (quasiIso (R := R) (A := A)).HasRightCalculusOfFractions := sorry

namespace QuasiIso

/-- Explicit `R`-linear enriched cochain quasi-isomorphisms form a saturated multiplicative
system. -/
@[stacks 09KX "saturation of enriched cochain quasi-isomorphisms over a linear base ring"]
def isSaturatedMultiplicativeSystem :
    (quasiIso (R := R) (A := A)).IsSaturatedMultiplicativeSystem := sorry

end QuasiIso

end CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Integral specialization of the explicit-base-ring enriched quasi-isomorphism property. -/
@[stacks 09KX "integral enriched cochain quasi-isomorphisms"]
abbrev quasiIso :
    MorphismProperty (DifferentialGradedCategory.K ℤ (CochainComplex A ℤ)) :=
  Over.quasiIso (R := ℤ) (A := A)

/-- Compatibility name for the integral left-calculus instance; the generic owner supplies it. -/
@[stacks 09KX "integral left calculus for enriched cochain quasi-isomorphisms"]
abbrev quasiIsoHasLeftCalculus :
    (quasiIso (A := A)).HasLeftCalculusOfFractions :=
  Over.quasiIsoHasLeftCalculus (R := ℤ) (A := A)

/-- Compatibility name for the integral right-calculus instance; the generic owner supplies it. -/
@[stacks 09KX "integral right calculus for enriched cochain quasi-isomorphisms"]
abbrev quasiIsoHasRightCalculus :
    (quasiIso (A := A)).HasRightCalculusOfFractions :=
  Over.quasiIsoHasRightCalculus (R := ℤ) (A := A)

namespace QuasiIso

/-- Compatibility name for saturation of the integral enriched quasi-isomorphism property. -/
@[stacks 09KX "integral saturation of enriched cochain quasi-isomorphisms"]
abbrev isSaturatedMultiplicativeSystem :
    (quasiIso (A := A)).IsSaturatedMultiplicativeSystem :=
  Over.QuasiIso.isSaturatedMultiplicativeSystem (R := ℤ) (A := A)

end QuasiIso

end CategoryTheory.CochainComplex.Enriched
