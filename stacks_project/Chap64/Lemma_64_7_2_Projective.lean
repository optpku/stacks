/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Definition_64_7_1_Projective
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Finite Filtered-Projective Objects

This module supplies the object property and full additive subcategory of finite
filtered-projective objects. Its canonical owner is `FilteredObject.Finite.FilteredProjective`;
the underlying condition remains the general `FilteredObject.IsFilteredProjective` predicate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

namespace FilteredObject.Finite.FilteredProjective

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  [HasCokernels C]

/-- The object property on finite filtered objects consisting of filtered-projective objects. -/
abbrev property (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :
    ObjectProperty (FilteredObject.Finite.category C) :=
  fun I => FilteredObject.IsFilteredProjective I.obj

/-- Membership in the finite filtered-projective object property is filtered-projectivity of the
underlying filtered object. -/
theorem property_iff (I : FilteredObject.Finite.category C) :
    property C I ↔ FilteredObject.IsFilteredProjective I.obj := sorry

/-- The full subcategory of finite filtered objects that are filtered projective. -/
abbrev category (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :=
  ObjectProperty.FullSubcategory (property C)

namespace category

/-- An object of the filtered-projective full subcategory has its canonical filtered-projective
instance. -/
instance isFilteredProjective (I : category C) : FilteredObject.IsFilteredProjective I.obj.obj :=
  sorry

end category

namespace property

/-- Finite filtered-projective objects are invariant under isomorphism. -/
instance closedUnderIsomorphisms :
    (property C).IsClosedUnderIsomorphisms := sorry

end property

/-- The inclusion of finite filtered-projective objects into finite filtered objects. -/
abbrev inclusion (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] :
    category C ⥤ FilteredObject.Finite.category C :=
  ObjectProperty.ι (property C)

/-- The forgetful functor from finite filtered-projective objects to the ambient category. -/
abbrev forget (C : Type u) [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
    [HasCokernels C] : category C ⥤ C :=
  inclusion C ⋙ FilteredObject.Finite.Forget.functor C

/-- Objectwise computation for the filtered-projective forgetful functor. -/
@[simp]
theorem forget_obj (I : category C) :
    (forget C).obj I = I.obj.obj.obj := sorry

/-- Morphismwise computation for the filtered-projective forgetful functor. -/
@[simp]
theorem forget_map {I J : category C} (f : I ⟶ J) :
    (forget C).map f = f.hom.hom.hom := sorry

section

variable {C : Type u} [_root_.CategoryTheory.Category.{v} C] [Abelian C]

namespace property

/-- Finite filtered-projective objects contain a zero object. -/
instance containsZero : (property C).ContainsZero := sorry

/-- Finite filtered-projective objects are closed under finite products. -/
instance closedUnderFiniteProducts :
    (property C).IsClosedUnderFiniteProducts := sorry

end property

namespace category

/-- The finite filtered-projective full subcategory inherits binary biproducts from its canonical
binary products and preadditive structure. -/
noncomputable instance hasBinaryBiproducts :
    HasBinaryBiproducts (category C) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end category

end

end FilteredObject.Finite.FilteredProjective

end CategoryTheory
