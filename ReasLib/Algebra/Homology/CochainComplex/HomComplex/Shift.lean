/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Module

/-!
# Module-valued Hom-complex shifts

This file retains the scalar-module structure on the degreewise Hom complex in any linear
preadditive category.  The complex is the canonical enriched Hom complex of the differential
graded category of cochain complexes.  The main API is the canonical first-variable shift
isomorphism; the specialization to complexes of modules also exposes their underlying linear
differential for differential graded module constructions.
-/

@[expose] public section

noncomputable section

universe w v u

open CategoryTheory

namespace CochainComplex.HomComplex

section Linear

variable (R : Type w) [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The canonical first-variable shift map
`Hom^•(M, N)[-k] ⟶ Hom^•(M⟦k⟧, N)`. -/
def leftShiftHom (M N : CochainComplex C ℤ) (k : ℤ) :
    (moduleComplex R M N)⟦-k⟧ ⟶ moduleComplex R (M⟦k⟧) N where
  f n := ModuleCat.ofHom <|
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n (sub_add_cancel n k)).toLinearMap
  comm' := sorry

/-- The inverse first-variable shift map
`Hom^•(M⟦k⟧, N) ⟶ Hom^•(M, N)[-k]`. -/
def leftShiftInv (M N : CochainComplex C ℤ) (k : ℤ) :
    moduleComplex R (M⟦k⟧) N ⟶ (moduleComplex R M N)⟦-k⟧ where
  f n := ModuleCat.ofHom <|
    (Cochain.leftShiftLinearEquiv R M N (n - k) k n
      (sub_add_cancel n k)).symm.toLinearMap
  comm' := sorry

/-- Remark 22.13.7 (0FQ9) (1): first-variable shift is an isomorphism of module-valued
cochain complexes, `Hom^•(M, N)[-k] ≅ Hom^•(M⟦k⟧, N)`. -/
@[stacks 0FQ9 "first-variable shift isomorphism of Hom complexes"]
def leftShiftIso (M N : CochainComplex C ℤ) (k : ℤ) :
    (moduleComplex R M N)⟦-k⟧ ≅ moduleComplex R (M⟦k⟧) N where
  hom := leftShiftHom R M N k
  inv := leftShiftInv R M N k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The degree-`n` component of the canonical first-variable shift map is the corresponding
linear shift equivalence. -/
@[simp]
theorem leftShiftHom_f (M N : CochainComplex C ℤ) (k n : ℤ) :
    (leftShiftHom R M N k).f n = ModuleCat.ofHom
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).toLinearMap := sorry

/-- The degree-`n` component of the inverse first-variable shift map is the inverse linear shift
equivalence. -/
@[simp]
theorem leftShiftInv_f (M N : CochainComplex C ℤ) (k n : ℤ) :
    (leftShiftInv R M N k).f n = ModuleCat.ofHom
      (Cochain.leftShiftLinearEquiv R M N (n - k) k n
        (sub_add_cancel n k)).symm.toLinearMap := sorry

/-- The forward map of `leftShiftIso` is `leftShiftHom`. -/
@[simp]
theorem leftShiftIso_hom (M N : CochainComplex C ℤ) (k : ℤ) :
    (leftShiftIso R M N k).hom = leftShiftHom R M N k := sorry

/-- The inverse map of `leftShiftIso` is `leftShiftInv`. -/
@[simp]
theorem leftShiftIso_inv (M N : CochainComplex C ℤ) (k : ℤ) :
    (leftShiftIso R M N k).inv = leftShiftInv R M N k := sorry

end Linear

end CochainComplex.HomComplex
