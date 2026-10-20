/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded

/-!
# Degree-Zero Category of a Differential Graded Category

This leaf isolates the ordinary category formed from all degree-zero morphisms
of a differential graded category.  The closed subcategory and its homotopy
quotient live in later leaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v}

open scoped DifferentialGradedCategory

/-- The category with the same objects as a differential graded category and all
degree-zero morphisms. -/
@[stacks 09L7 "degree-zero category of a differential graded category"]
structure DegreeZero (R : Type u) [CommRing R] (C : Type v) where
  /-- The underlying object of the differential graded category. -/
  obj : C

namespace DegreeZero

/-- A `DegreeZero` object can be used as its underlying object of the differential graded
category. -/
@[stacks 09L7 "degree-zero object coercion"]
instance : CoeTC (DegreeZero R C) C where
  coe X := X.obj

/-- Constructing a degree-zero object and coercing it back recovers the original object. -/
@[simp, stacks 09L7 "degree-zero category object coercion"]
theorem coe_mk (X : C) : ((⟨X⟩ : DegreeZero R C) : C) = X := sorry

end DegreeZero

variable [D : DifferentialGradedCategory R C]

namespace DegreeZero

/-- All degree-zero morphisms form the degree-zero category of a differential graded category. -/
@[stacks 09L7 "category structure on all degree-zero morphisms"]
instance : Category (DegreeZero R C) where
  Hom X Y := ((X : C) ⟶[0] (Y : C))
  id X := D.id X
  comp f g := D.comp g f
  id_comp f := D.comp_id f
  comp_id f := D.id_comp f
  assoc f g h := D.comp_assoc_zero h g f

/-- The additive commutative group on a degree-zero hom-space. -/
@[stacks 09L7 "additive degree-zero hom groups"]
instance degreeZeroHomAddCommGroup (X Y : DegreeZero R C) : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs <| AddCommGroup (X.obj ⟶[0] Y.obj)

/-- The canonical `R`-module structure on a degree-zero hom-space. -/
@[stacks 09L7 "module structure on degree-zero hom groups"]
instance degreeZeroHomModule (X Y : DegreeZero R C) : Module R (X ⟶ Y) :=
  inferInstanceAs <| Module R (X.obj ⟶[0] Y.obj)

/-- Addition is compatible with postcomposition in the degree-zero category. -/
@[stacks 09L7 "postcomposition and addition in the degree-zero category"]
theorem degreeZeroPreadditive_add_comp (X Y Z : DegreeZero R C)
    (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (f + f') ≫ g = f ≫ g + f' ≫ g := sorry

/-- Addition is compatible with precomposition in the degree-zero category. -/
@[stacks 09L7 "precomposition and addition in the degree-zero category"]
theorem degreeZeroPreadditive_comp_add (X Y Z : DegreeZero R C)
    (f : X ⟶ Y) (g g' : Y ⟶ Z) :
    f ≫ (g + g') = f ≫ g + f ≫ g' := sorry

/-- All degree-zero morphisms form a preadditive category. -/
@[stacks 09L7 "preadditive structure on the degree-zero category"]
instance degreeZeroPreadditive : Preadditive (DegreeZero R C) where
  homGroup X Y := degreeZeroHomAddCommGroup X Y
  add_comp X Y Z f f' g := degreeZeroPreadditive_add_comp X Y Z f f' g
  comp_add X Y Z f g g' := degreeZeroPreadditive_comp_add X Y Z f g g'

/-- Scalar multiplication is compatible with postcomposition in the degree-zero category. -/
@[stacks 09L7 "postcomposition and scalar multiplication in the degree-zero category"]
theorem degreeZeroLinear_smul_comp (X Y Z : DegreeZero R C) (r : R)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) := sorry

/-- Scalar multiplication is compatible with precomposition in the degree-zero category. -/
@[stacks 09L7 "precomposition and scalar multiplication in the degree-zero category"]
theorem degreeZeroLinear_comp_smul (X Y Z : DegreeZero R C)
    (f : X ⟶ Y) (r : R) (g : Y ⟶ Z) :
    f ≫ (r • g) = r • (f ≫ g) := sorry

/-- The degree-zero category of a differential graded category is canonically `R`-linear. -/
@[stacks 09L7 "linear structure on the degree-zero category"]
instance degreeZeroLinear : Linear R (DegreeZero R C) where
  homModule X Y := degreeZeroHomModule X Y
  smul_comp := degreeZeroLinear_smul_comp
  comp_smul := degreeZeroLinear_comp_smul

end DegreeZero

end DifferentialGradedCategory
