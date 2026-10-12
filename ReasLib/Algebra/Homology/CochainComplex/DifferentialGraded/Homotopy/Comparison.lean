/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Linear
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Enriched cochain homotopy over a linear base ring

Let `C` be an `R`-linear category.  The explicit enrichment
`CochainComplex.differentialGradedCategory C R` has a homotopy category whose morphisms are
closed degree-zero cochains modulo cochain homotopy.  This file compares that category with
Mathlib's ordinary `HomotopyCategory C (ComplexShape.up ℤ)`.

The comparison is parameterized by the linear base ring even though its target is independent
of that choice.  This is useful when an enriched construction is naturally linear over a ring
other than `ℤ`.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Closed degree-zero cochains for the explicit `R`-linear enrichment of cochain complexes. -/
@[stacks 09L7 "closed cochain maps over a linear base ring"]
abbrev ClosedHom (R : Type r) [CommRing R]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    (X Y : CochainComplex C ℤ) :=
  Cocycle X Y 0

/-- Homotopy of closed cochains in the explicit `R`-linear cochain-complex enrichment. -/
@[stacks 09JN "cochain homotopy over a linear base ring"]
abbrev Homotopic {X Y : CochainComplex C ℤ} (f g : ClosedHom R X Y) : Prop :=
  @DifferentialGradedCategory.Homotopic R _ _
    (CochainComplex.differentialGradedCategory C R) X Y f g

/-- Convert a closed cochain in the explicit `R`-linear enrichment to an ordinary morphism of
cochain complexes. -/
@[stacks 09L7 "closed cochain to ordinary cochain map"]
def toHom {X Y : CochainComplex C ℤ} (f : ClosedHom R X Y) : X ⟶ Y :=
  Cocycle.homOf f

/-- Regard an ordinary morphism of cochain complexes as a closed cochain in the explicit
`R`-linear enrichment. -/
@[stacks 09L7 "ordinary cochain map to closed cochain"]
def ofHom {X Y : CochainComplex C ℤ} (f : X ⟶ Y) : ClosedHom R X Y :=
  Cocycle.ofHom f

/-- Ordinary cochain maps and closed cochains in the explicit `R`-linear enrichment are
additively equivalent. -/
@[stacks 09L7 "closed and ordinary cochain map equivalence"]
def compEquiv (X Y : CochainComplex C ℤ) : ClosedHom R X Y ≃+ (X ⟶ Y) :=
  (Cocycle.equivHom X Y).symm

/-- Enriched homotopy for the explicit `R`-linear cochain enrichment is exactly ordinary
cochain homotopy after applying `toHom`. -/
@[stacks 09JN "enriched and ordinary cochain homotopy equivalence"]
theorem homotopic_iff {X Y : CochainComplex C ℤ} {f g : ClosedHom R X Y} :
    Homotopic f g ↔ Nonempty (_root_.Homotopy (toHom f) (toHom g)) := sorry

/-- Enriched homotopy of closed cochains becomes ordinary cochain homotopy. -/
@[stacks 09JN "closed cochain homotopy comparison"]
theorem toHom_homotopy {X Y : CochainComplex C ℤ} {f g : ClosedHom R X Y}
    (h : Homotopic f g) : Nonempty (_root_.Homotopy (toHom f) (toHom g)) := sorry

/-- Enriched-homotopic closed cochains have equal images in Mathlib's homotopy category. -/
@[stacks 09JQ "homotopy quotient comparison"]
theorem quotient_map_sound {X Y : CochainComplex C ℤ} {f g : ClosedHom R X Y}
    (h : Homotopic f g) :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (toHom f) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (toHom g) := sorry

/-- Compare the homotopy category of the explicit `R`-linear cochain enrichment with
Mathlib's ordinary cochain homotopy category. -/
@[stacks 09JQ "cochain homotopy comparison over a linear base ring"]
def toMathlib :
    DifferentialGradedCategory.K R (CochainComplex C ℤ) ⥤
      HomotopyCategory C (ComplexShape.up ℤ) where
  obj X := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X.obj
  map {X Y} f :=
    _root_.Quotient.lift
      (fun g : ClosedHom R X.obj Y.obj ↦
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (toHom g))
      (fun _ _ h ↦ quotient_map_sound h) f
  map_id := sorry
  map_comp := sorry

/-- The enriched-to-ordinary homotopy comparison preserves the ambient `R`-linear structure. -/
@[stacks 09JQ "linearity of the enriched cochain homotopy comparison"]
noncomputable instance toMathlib_linear :
    (toMathlib (R := R) (C := C)).Linear R := sorry

/-- Compare Mathlib's ordinary cochain homotopy category with the homotopy category of the
explicit `R`-linear cochain enrichment. -/
@[stacks 09JQ "ordinary to enriched cochain homotopy comparison"]
def fromMathlib :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤
      DifferentialGradedCategory.K R (CochainComplex C ℤ) where
  obj X := ⟨X.as⟩
  map f :=
    @DifferentialGradedCategory.CompHom.toHomotopyClass R _ _
      (CochainComplex.differentialGradedCategory C R) _ _
      (ofHom (R := R) (C := C) f.out)
  map_id := sorry
  map_comp := sorry

/-- The ordinary-to-enriched homotopy comparison preserves the ambient `R`-linear structure. -/
@[stacks 09JQ "linearity of the ordinary cochain homotopy comparison"]
noncomputable instance fromMathlib_linear :
    (fromMathlib (R := R) (C := C)).Linear R := sorry

/-- Explicit quasi-inverse data for the `R`-linear enriched-to-ordinary homotopy comparison. -/
@[stacks 09JQ "cochain homotopy comparison quasi-inverse"]
def comparisonQuasiInverse : Functor.QuasiInverse (toMathlib (R := R) (C := C)) where
  inverse := fromMathlib
  unitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) (fun _ ↦ sorry)
  counitIso := NatIso.ofComponents (fun X ↦ Iso.refl X) (fun _ ↦ sorry)

/-- The homotopy category of the explicit `R`-linear cochain enrichment is canonically
equivalent to Mathlib's ordinary cochain homotopy category. -/
@[stacks 09JQ "enriched cochain homotopy equivalence over a linear base ring"]
def equivalence :
    DifferentialGradedCategory.K R (CochainComplex C ℤ) ≌
      HomotopyCategory C (ComplexShape.up ℤ) :=
  (comparisonQuasiInverse (R := R) (C := C)).adjointifyUnit

/-- The comparison equivalence uses `toMathlib` in the forward direction. -/
@[simp, stacks 09JQ "cochain homotopy comparison forward functor"]
theorem equivalence_functor :
    (equivalence (R := R) (C := C)).functor = toMathlib := sorry

/-- The comparison equivalence uses `fromMathlib` in the inverse direction. -/
@[simp, stacks 09JQ "cochain homotopy comparison inverse functor"]
theorem equivalence_inverse :
    (equivalence (R := R) (C := C)).inverse = fromMathlib := sorry

end CategoryTheory.CochainComplex.Enriched.Over
