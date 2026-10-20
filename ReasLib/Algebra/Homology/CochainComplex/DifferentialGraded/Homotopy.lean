/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Comparison
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.QuasiIso
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived

/-!
# Comparison of enriched and ordinary cochain homotopy categories

The differential graded category of cochain complexes produces its own closed and homotopy
categories.  Mathlib also has the ordinary quotient `HomotopyCategory`.  This file owns the
explicit comparison equivalence between those two homotopy presentations.  Quasi-isomorphism
and derived-localization APIs live in the sibling `Homotopy.QuasiIso` and `Homotopy.Derived`
leaves.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace CategoryTheory.CochainComplex.Enriched

section Comparison

variable {A : Type u} [Category.{v} A] [Preadditive A]

/-- Convert a closed degree-zero morphism in the integral cochain-complex enrichment to an
ordinary morphism of cochain complexes. -/
abbrev toHom {X Y : CochainComplex A ℤ} (f : CompHom X Y) : X ⟶ Y :=
  Over.toHom (R := ℤ) f

/-- Regard an ordinary morphism of cochain complexes as a closed degree-zero morphism in the
integral enrichment. -/
abbrev ofHom {X Y : CochainComplex A ℤ} (f : X ⟶ Y) : CompHom X Y :=
  Over.ofHom (R := ℤ) f

/-- Ordinary cochain maps and closed degree-zero morphisms in the integral enrichment are
additively equivalent. -/
abbrev compEquiv (X Y : CochainComplex A ℤ) : CompHom X Y ≃+ (X ⟶ Y) :=
  Over.compEquiv (R := ℤ) X Y

/-- Enriched homotopy of closed cochains becomes ordinary cochain homotopy. -/
theorem toHom_homotopy {X Y : CochainComplex A ℤ} {f g : CompHom X Y}
    (h : Homotopic X Y f g) : Nonempty (_root_.Homotopy (toHom f) (toHom g)) := sorry

/-- Enriched-homotopic closed cochains have equal images in Mathlib's homotopy category. -/
theorem quotient_map_sound {X Y : CochainComplex A ℤ} {f g : CompHom X Y}
    (h : Homotopic X Y f g) :
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (toHom f) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (toHom g) := sorry

/-- Compare the homotopy category of the cochain-complex enrichment with Mathlib's ordinary
cochain homotopy category. -/
@[stacks 09JQ "enriched cochain homotopy comparison"]
def toMathlib :
    DifferentialGradedCategory.K ℤ (CochainComplex A ℤ) ⥤
      HomotopyCategory A (ComplexShape.up ℤ) :=
  Over.toMathlib (R := ℤ)

/-- Compare Mathlib's ordinary cochain homotopy category with the homotopy category of the
cochain-complex enrichment. -/
def fromMathlib :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤
      DifferentialGradedCategory.K ℤ (CochainComplex A ℤ) :=
  Over.fromMathlib (R := ℤ)

/-- Explicit quasi-inverse data for the integral enriched-to-ordinary homotopy comparison. -/
abbrev comparisonQuasiInverse : Functor.QuasiInverse (toMathlib (A := A)) :=
  Over.comparisonQuasiInverse (R := ℤ)

/-- The enriched and ordinary homotopy categories of cochain complexes are canonically
equivalent. -/
@[stacks 09JQ "enriched and ordinary cochain homotopy categories"]
def equivalence :
    DifferentialGradedCategory.K ℤ (CochainComplex A ℤ) ≌
      HomotopyCategory A (ComplexShape.up ℤ) :=
  Over.equivalence (R := ℤ)

/-- The comparison equivalence uses the explicit functor `toMathlib` in the forward
direction. -/
@[simp]
theorem equivalence_functor : (equivalence (A := A)).functor = toMathlib := sorry

/-- The comparison equivalence uses the explicit functor `fromMathlib` in the inverse
direction. -/
@[simp]
theorem equivalence_inverse : (equivalence (A := A)).inverse = fromMathlib := sorry

end Comparison

end CategoryTheory.CochainComplex.Enriched
