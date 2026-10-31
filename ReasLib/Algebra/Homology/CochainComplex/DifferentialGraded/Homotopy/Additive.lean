/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Comparison

/-!
# Additive structure of enriched cochain homotopy categories

The actual closed-cochain comparison preserves addition on homotopy classes. Its explicit
inverse then transports the zero object and binary biproduct diagrams from Mathlib's homotopy
category. These instances apply only to the canonical cochain enrichment over `R`.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory CategoryTheory.Limits
open DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The closed-cochain additive equivalence and the ordinary homotopy quotient induce an
additive comparison on the enriched homotopy category. -/
noncomputable instance toMathlib_additive :
    (toMathlib (R := R) (C := C)).Additive := by
  constructor
  intro X Y f g
  refine _root_.Quotient.inductionOn₂ f g ?_
  intro f₀ g₀
  change (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((compEquiv (R := R) X.obj Y.obj) (f₀ + g₀)) =
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((compEquiv (R := R) X.obj Y.obj) f₀) +
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((compEquiv (R := R) X.obj Y.obj) g₀)
  erw [(compEquiv (R := R) X.obj Y.obj).map_add, Functor.map_add]

/-- The supplied inverse comparison is additive because it is inverse to the additive
comparison equivalence. -/
noncomputable instance fromMathlib_additive :
    (fromMathlib (R := R) (C := C)).Additive := by
  let e := equivalence (R := R) (C := C)
  letI : e.functor.Additive := by
    change (toMathlib (R := R) (C := C)).Additive
    infer_instance
  change e.inverse.Additive
  exact Equivalence.inverse_additive e

/-- The enriched cochain homotopy category has the image under `fromMathlib` of the ordinary
homotopy category's zero object. -/
noncomputable instance kHasZeroObject [HasZeroObject C] :
    HasZeroObject (DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  Functor.hasZeroObject_of_additive (fromMathlib (R := R) (C := C))

/-- Degreewise binary products give biproducts of complexes. Their images under the ordinary
homotopy quotient and the explicit inverse comparison give binary biproducts in enriched `K`.
The comparison unit transports the two summands to the requested enriched objects. -/
noncomputable instance kHasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryBiproducts (DifferentialGradedCategory.K R (CochainComplex C ℤ)) := by
  letI : HasBinaryProducts (CochainComplex C ℤ) := inferInstance
  letI : HasBinaryBiproducts (CochainComplex C ℤ) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  letI : PreservesBinaryBiproducts (HomotopyCategory.quotient C (ComplexShape.up ℤ)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  letI : HasBinaryBiproducts (HomotopyCategory C (ComplexShape.up ℤ)) :=
    { has_binary_biproduct := fun X Y => by
        obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
        exact Functor.hasBinaryBiproduct_of_preserves
          (HomotopyCategory.quotient C (ComplexShape.up ℤ)) X Y }
  let e := equivalence (R := R) (C := C)
  letI : e.inverse.Additive := by
    change (fromMathlib (R := R) (C := C)).Additive
    infer_instance
  letI : PreservesBinaryBiproducts e.inverse :=
    preservesBinaryBiproducts_of_preservesBiproducts e.inverse
  constructor
  intro X Y
  letI : HasBinaryBiproduct
      (e.inverse.obj (e.functor.obj X)) (e.inverse.obj (e.functor.obj Y)) :=
    Functor.hasBinaryBiproduct_of_preserves e.inverse (e.functor.obj X) (e.functor.obj Y)
  let eX : e.inverse.obj (e.functor.obj X) ≅ X := (e.unitIso.app X).symm
  let eY : e.inverse.obj (e.functor.obj Y) ≅ Y := (e.unitIso.app Y).symm
  exact hasBinaryBiproduct_of_iso eX eY

end CategoryTheory.CochainComplex.Enriched.Over
