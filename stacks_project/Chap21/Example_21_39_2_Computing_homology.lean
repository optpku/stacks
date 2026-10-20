/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology.Computation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Example 21.39.2 (08PG): category homology is computed by the explicit bar complex on
composable arrows. -/
@[stacks 08PG "category homology bar complex"]
#check @CategoryTheory.CategoryHomology.simplicialObject

@[stacks 08PG "category homology bar complex"]
#check @CategoryTheory.CategoryHomology.complex

@[stacks 08PG "canonical bar colimit augmentation"]
#check @CategoryTheory.CategoryHomology.Bar.colimitAugmentation

@[stacks 08PG "category-homology bar chain augmentation"]
#check @CategoryTheory.CategoryHomology.Bar.chainAugmentation

@[stacks 08PG "zeroth bar homology is presheaf colimit"]
#check @CategoryTheory.CategoryHomology.Bar.zeroIso

@[stacks 08PG "category homology bar delta functor"]
#check @CategoryTheory.CategoryHomology.Bar.deltaFunctor

section UniversalComparison

universe u v w

variable {C : Type u} [Category.{v} C] [UnivLE.{max u v, w}]
variable [Limits.HasColimitsOfShape Cᵒᵖ AddCommGrpCat.{w}]

/- Example 21.39.2 (08PG): the homological universal property extends degree-zero maps into
bar homology. -/
@[stacks 08PG "terminal universal property of bar homology"]
#check (HomologicalDeltaFunctor.IsUniversal.existsUnique_hom
  (F := CategoryHomology.Bar.deltaFunctor (C := C)) :
  (G : HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w}) →
  (t : (G 0).obj ⟶ (CategoryHomology.Bar.deltaFunctor (C := C) 0).obj) →
  ∃! τ : G ⟶ CategoryHomology.Bar.deltaFunctor (C := C), τ.app 0 = t)

/- Example 21.39.2 (08PG): universal homological delta functors extending colimit compare
canonically with the explicit bar delta functor. -/
@[stacks 08PG "universal category-homology comparison with the bar delta functor"]
#check (CategoryHomology.Bar.universalIso (C := C) :
  (T : HomologicalDeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{w}) AddCommGrpCat.{w}) →
  [T.IsUniversal] →
  (e₀ : (T 0).obj ≅ (Limits.colim : (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})) →
  T ≅ CategoryHomology.Bar.deltaFunctor (C := C))

end UniversalComparison

@[stacks 08PG "category homology bar complex computation"]
#check @CategoryTheory.CategoryHomology.isomorphic_homology_complex

@[stacks 08PF "derived category homology coefficient functor"]
#check @CategoryTheory.CategoryHomology.coefficientFunctor

@[stacks 08PF "derived category homology coefficient functor object formula"]
#check @CategoryTheory.CategoryHomology.coefficientFunctor_obj

@[stacks 08PG "bar category homology coefficient functor"]
#check @CategoryTheory.CategoryHomology.Bar.coefficientFunctor

@[stacks 08PG "bar category homology coefficient functor object formula"]
#check @CategoryTheory.CategoryHomology.Bar.coefficientFunctor_obj
